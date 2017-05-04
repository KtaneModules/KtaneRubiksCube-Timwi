﻿using System;
using RubiksCube;
using System.Collections;
using System.Collections.Generic;
using System.Linq;
using UnityEngine;
using Rnd = UnityEngine.Random;

/// <summary>
/// On the Subject of Rubik’s Cube
/// Created by Timwi and Freelancer1025
/// </summary>
public class RubiksCubeModule : MonoBehaviour
{
    public KMBombInfo Bomb;
    public KMBombModule Module;
    public KMAudio Audio;
    public KMSelectable MainSelectable;

    public KMSelectable Reset;
    public KMSelectable[] Pushers;
    public Material[] StickerMaterials;

    public Transform OffAxis;
    public Transform OnAxis;

    public Mesh ArrowNSWE;
    public Mesh Arrow;

    private Transform[,,] _cubeletsSolved;
    private Transform[,,] _cubelets;

    private Queue<object> _queue = new Queue<object>();
    private Stack<FaceRotation> _performedMoves = new Stack<FaceRotation>();
    private Pusher[] _pushers;

    private bool _isSolved = false;
    private Pusher _selectedPusher = null;
    private int[] _columnShifts;
    private int _serialIgnore, _colR;

    private int _moduleId;
    private static int _moduleIdCounter = 1;

    sealed class Pusher
    {
        public FaceRotation[] Moves { get; private set; }
        public int[] MoveIndexes { get; private set; }
        public Vector3 LocalPosition { get; private set; }
        public Vector3[] LocalEulerAngles { get; private set; }
        public KMSelectable Selectable { get; private set; }
        public MeshRenderer MeshRenderer { get; private set; }
        public MeshFilter MeshFilter { get; private set; }
        public MeshFilter HighlightMeshFilter { get; private set; }

        public Pusher(KMSelectable selectable, FaceRotation[] moves, int[] moveIndexes, Vector3 localPos, params Vector3[] localAngles)
        {
            Moves = moves;
            MoveIndexes = moveIndexes;
            LocalPosition = localPos;
            LocalEulerAngles = localAngles;
            Selectable = selectable;

            MeshRenderer = Selectable.GetComponent<MeshRenderer>();
            MeshFilter = Selectable.GetComponent<MeshFilter>();
            HighlightMeshFilter = Selectable.transform.Find("Highlight").Find("Highlight(Clone)").GetComponent<MeshFilter>();
        }

        public KMSelectable Instantiate(KMSelectable template, Transform newParent)
        {
            var obj = UnityEngine.Object.Instantiate(template);
            obj.transform.parent = newParent;
            obj.transform.localEulerAngles = LocalEulerAngles[0];
            obj.transform.localPosition = LocalPosition;
            obj.transform.localScale = new Vector3(1, 1, 1);
            return obj;
        }
    }

    void Start()
    {
        _moduleId = _moduleIdCounter++;
        //Cube.localEulerAngles = new Vector3(25, 70, 60);

        var colors = Enumerable.Range(0, 6).ToArray().Shuffle();
        var colorNames = "Yellow|Blue|Red|Green|Orange|White".Split('|');
        var faces = "ULFDRB";
        Debug.LogFormat("[Rubik’s Cube #{0}] Face colors: {1}", _moduleId, string.Join(", ", Enumerable.Range(0, 6).Select(i => string.Format("{0}={1}", faces[i], colorNames[colors[i]])).ToArray()));
        _columnShifts = newArray(colors[0] + 1, colors[1] + 1, colors[2] + 1);
        _serialIgnore = colors[3];
        _colR = colors[4];
        _cubelets = new Transform[3, 3, 3];
        for (int x = 0; x < 3; x++)
            for (int y = 0; y < 3; y++)
                for (int z = 0; z < 3; z++)
                    if (x != 1 || y != 1 || z != 1)
                    {
                        _cubelets[x, y, z] = OffAxis.Find(string.Format("Cubelet ({0}, {1}, {2})", x, y, z));
                        for (int i = 0; i < faces.Length; i++)
                        {
                            var sticker = _cubelets[x, y, z].Find(string.Format("{0} sticker", faces[i]));
                            if (sticker != null)
                                sticker.GetComponent<MeshRenderer>().material = StickerMaterials[colors[i]];
                        }
                    }

        _cubeletsSolved = _cubelets;
        Module.OnActivate += ActivateModule;
    }

    private void SetPusherEvents(Pusher pusher)
    {
        pusher.Selectable.OnInteract += delegate
        {
            if (_isSolved)
                return false;

            if (_selectedPusher == null)
            {
                _selectedPusher = pusher;
                pusher.MeshFilter.mesh = ArrowNSWE;
                pusher.MeshRenderer.enabled = true;
            }
            else if (_selectedPusher == pusher)
            {
                _selectedPusher = null;
                pusher.MeshRenderer.enabled = false;
            }
            else
            {
                foreach (var move in _moves.Values)
                {
                    var ix1 = Array.IndexOf(_selectedPusher.Moves, move);
                    var ix2 = Array.IndexOf(pusher.Moves, move);
                    if (ix1 != -1 && ix2 != -1 && pusher.MoveIndexes[ix2] > _selectedPusher.MoveIndexes[ix1])
                    {
                        _queue.Enqueue(move);
                        _performedMoves.Push(move);
                        _selectedPusher.MeshRenderer.enabled = false;
                        _selectedPusher = null;
                        pusher.HighlightMeshFilter.mesh = ArrowNSWE;
                        break;
                    }
                }
            }
            return false;
        };

        pusher.Selectable.OnHighlight += delegate
        {
            if (_isSolved || _selectedPusher == null)
                return;

            foreach (var move in _moves.Values)
            {
                var ix1 = Array.IndexOf(_selectedPusher.Moves, move);
                var ix2 = Array.IndexOf(pusher.Moves, move);
                if (ix1 != -1 && ix2 != -1 && pusher.MoveIndexes[ix2] > _selectedPusher.MoveIndexes[ix1])
                {
                    _selectedPusher.MeshFilter.mesh = Arrow;
                    _selectedPusher.Selectable.transform.localEulerAngles = _selectedPusher.LocalEulerAngles[ix1];
                    pusher.HighlightMeshFilter.mesh = Arrow;
                    pusher.Selectable.transform.localEulerAngles = pusher.LocalEulerAngles[ix2];
                    return;
                }
            }

            _selectedPusher.MeshFilter.mesh = ArrowNSWE;
        };

        pusher.Selectable.OnDeselect += delegate
        {
            if (!_isSolved && _selectedPusher != null)
            {
                _selectedPusher.MeshFilter.mesh = ArrowNSWE;
                pusher.HighlightMeshFilter.mesh = ArrowNSWE;
            }
        };
    }

    private static T[] newArray<T>(params T[] array) { return array; }

    void ActivateModule()
    {
        var pusherMoveInfos = @"
            B  = F002 C002 E311 B311 
            B’ = B111 E111 C022 F022 
            D  = B211 H211 A201 D201 
            D’ = D001 A001 H011 B011 
            F  = H111 K111 I022 L022 
            F’ = L002 I002 K311 H311 
            L  = C032 I032 G301 A301 
            L’ = A101 G101 I012 C012 
            R  = D101 J101 L012 F012 
            R’ = F032 L032 J301 D301 
            U  = J001 G001 K011 E011 
            U’ = E211 K211 G201 J201 
        "
            .Split('\n')
            .Select(s => s.Trim())
            .Where(s => s.Length > 1)
            .Select(s => s.Split('='))
            .Select(inf => new
            {
                Move = _moves[inf[0].Trim()],
                Pushers = inf[1].Trim().Split(' ').Select(str => Pushers[str[0] - 'A']).ToArray(),
                Rotations = inf[1].Trim().Split(' ').Select(str => new Vector3((str[1] - '0') * 90, (str[2] - '0') * 90, (str[3] - '0') * 90)).ToArray()
            })
            .ToArray();

        _pushers = Pushers.Select((obj, ix) => new Pusher(
            selectable: obj,
            moves: pusherMoveInfos.Where(inf => inf.Pushers.Contains(obj)).Select(inf => inf.Move).ToArray(),
            moveIndexes: pusherMoveInfos.Where(inf => inf.Pushers.Contains(obj)).Select(inf => Array.IndexOf(inf.Pushers, obj)).ToArray(),
            localPos: ix % 3 == 0 ? new Vector3(3.01f, 4 * (ix / 9) - 2, 4 * ((ix / 3) % 3) - 2) : ix % 3 == 1 ? new Vector3(4 * (ix / 9) - 2, 4 * ((ix / 3) % 3) - 2, -3.01f) : new Vector3(4 * (ix / 9) - 2, 3.01f, 4 * ((ix / 3) % 3) - 2),
            localAngles: pusherMoveInfos.Where(inf => inf.Pushers.Contains(obj)).Select(inf => inf.Rotations[Array.IndexOf(inf.Pushers, obj)]).ToArray()
        )).ToArray();
        foreach (var pusher in _pushers)
            SetPusherEvents(pusher);

        var table = @"L’,F’;D’,U’;U,B’;F,B;L,D;R’,U;U’,F;B’,L’;B,R;D,L;R,D’;F’,R’".Split(';').Select(row => row.Split(',').Select(str => _moves[str]).ToArray()).ToArray();
        Debug.LogFormat("[Rubik’s Cube #{0}] Column shifts: U={1}, L={2}, F={3}", _moduleId, _columnShifts[0], _columnShifts[1], _columnShifts[2]);
        var ser = Bomb.GetSerialNumber().Remove(_serialIgnore, 1);
        var rows = ser.Select(ch => ch >= '0' && ch <= '9' ? ch - '0' : ch - 'A' + 10).Select(n => (n / 3 + _columnShifts[n % 3]) % table.Length).ToArray();
        Debug.LogFormat("[Rubik’s Cube #{0}] Ignoring serial number character #{1}: {2}", _moduleId, _serialIgnore + 1, string.Join(", ", rows.Select((r, rIx) => string.Format("{0}={1}/{2}", ser[rIx], table[r][0].Name, table[r][1].Name)).ToArray()));
        FaceRotation[] moves;
        if (_colR >= 1 && _colR <= 3)
        {
            moves = rows.SelectMany(r => table[r]).ToArray();
            Debug.LogFormat("[Rubik’s Cube #{0}] R face is red/green/blue. Moves now: {1}", _moduleId, string.Join(" ", moves.Select(m => m.Name).ToArray()));
        }
        else
        {
            moves = rows.Select(r => table[r][0]).Concat(rows.Select(r => table[r][1])).ToArray();
            Debug.LogFormat("[Rubik’s Cube #{0}] R face is NOT red/green/blue. Moves now: {1}", _moduleId, string.Join(" ", moves.Select(m => m.Name).ToArray()));
        }

        var msg = "";
        switch (_colR)
        {
            case 2: // red
            case 0: // yellow
                msg = "R face is red/yellow: change the first five moves to their opposites. ";
                for (int i = 0; i < 5; i++)
                    moves[i] = moves[i].Reverse;
                break;

            case 3: // green
            case 5: // white
                msg = "R face is green/white: reverse the order of all the moves. ";
                for (int i = 0; i < 5; i++)
                {
                    var t = moves[i];
                    moves[i] = moves[9 - i];
                    moves[9 - i] = t;
                }
                break;
        }

        Debug.LogFormat("[Rubik’s Cube #{0}] {1}Solution: {2}", _moduleId, msg, string.Join(" ", moves.Select(m => m.Name).ToArray()));

        _queue.Enqueue(90);
        foreach (var move in moves.Reverse())
            _queue.Enqueue(move.Reverse);
        _queue.Enqueue(5);

        StartCoroutine(PerformMoves());

        Bomb.OnBombExploded += delegate
        {
            if (!_isSolved && _performedMoves.Count > 0)
                Debug.LogFormat("[Rubik’s Cube #{0}] Moves performed before reset: {1}", _moduleId, string.Join(" ", _performedMoves.Reverse().Select(m => m.Name).ToArray()));
        };

        Reset.OnInteract += delegate
        {
            Reset.AddInteractionPunch();
            Audio.PlayGameSoundAtTransform(KMSoundOverride.SoundEffect.ButtonPress, Reset.transform);
            if (_isSolved || _performedMoves.Count == 0)
                return false;
            Debug.LogFormat("[Rubik’s Cube #{0}] Moves performed before reset: {1}", _moduleId, string.Join(" ", _performedMoves.Reverse().Select(m => m.Name).ToArray()));
            _queue.Enqueue(18);
            while (_performedMoves.Count > 0)
                _queue.Enqueue(_performedMoves.Pop().Reverse);
            _queue.Enqueue(5);
            return false;
        };

        MainSelectable.OnCancel += delegate
        {
            if (_selectedPusher != null)
            {
                _selectedPusher.MeshRenderer.enabled = false;
                _selectedPusher = null;
            }
            return true;
        };
    }

    private IEnumerator PerformMoves()
    {
        int speed = 5;
        while (!_isSolved)
        {
            yield return null;
            if (_queue.Count > 0)
            {
                var obj = _queue.Dequeue();
                if (obj is int)
                    speed = (int) obj;
                else if (obj is FaceRotation)
                {
                    foreach (var p in Pushers)
                        p.gameObject.SetActive(false);
                    foreach (var item in PerformRotation((FaceRotation) obj, speed))
                        yield return item;

                    if (speed == 5 && isSolved(_cubelets))
                    {
                        _isSolved = true;
                        Module.HandlePass();
                        Debug.LogFormat("[Rubik’s Cube #{0}] Module solved.", _moduleId);
                        if (_selectedPusher != null)
                        {
                            _selectedPusher.MeshRenderer.enabled = false;
                            _selectedPusher = null;
                        }
                        Reset.gameObject.SetActive(false);
                        yield break;
                    }

                    foreach (var p in Pushers)
                        p.gameObject.SetActive(true);
                }
            }
        }
    }

    private bool isSolved(Transform[,,] cubelets)
    {
        for (int x = 0; x < 3; x++)
            for (int y = 0; y < 3; y++)
                for (int z = 0; z < 3; z++)
                    if (cubelets[x, y, z] != _cubeletsSolved[x, y, z])
                        return false;
        return true;
    }

    sealed class FaceRotation
    {
        public string Name { get; private set; }
        public Func<int, int, int, bool> OnAxis { get; private set; }
        public Func<float, Vector3> Rotation { get; private set; }
        public Func<int, int, int, int> MapX { get; private set; }
        public Func<int, int, int, int> MapY { get; private set; }
        public Func<int, int, int, int> MapZ { get; private set; }
        public FaceRotation(string name, Func<int, int, int, bool> onAxis, Func<float, Vector3> rotation, Func<int, int, int, int> mapX, Func<int, int, int, int> mapY, Func<int, int, int, int> mapZ)
        {
            Name = name;
            OnAxis = onAxis;
            Rotation = rotation;
            MapX = mapX;
            MapY = mapY;
            MapZ = mapZ;
        }
        public FaceRotation Reverse { get; set; }
    }

    private static Dictionary<string, FaceRotation> _moves;

    static RubiksCubeModule()
    {
        var moves = newArray(
            new FaceRotation("F", (x, y, z) => z == 0, i => new Vector3(i, 0, 0), (x, y, z) => y, (x, y, z) => 2 - x, (x, y, z) => z),
            new FaceRotation("F’", (x, y, z) => z == 0, i => new Vector3(-i, 0, 0), (x, y, z) => 2 - y, (x, y, z) => x, (x, y, z) => z),
            new FaceRotation("B", (x, y, z) => z == 2, i => new Vector3(-i, 0, 0), (x, y, z) => 2 - y, (x, y, z) => x, (x, y, z) => z),
            new FaceRotation("B’", (x, y, z) => z == 2, i => new Vector3(i, 0, 0), (x, y, z) => y, (x, y, z) => 2 - x, (x, y, z) => z),
            new FaceRotation("L", (x, y, z) => x == 0, i => new Vector3(0, 0, -i), (x, y, z) => x, (x, y, z) => z, (x, y, z) => 2 - y),
            new FaceRotation("L’", (x, y, z) => x == 0, i => new Vector3(0, 0, i), (x, y, z) => x, (x, y, z) => 2 - z, (x, y, z) => y),
            new FaceRotation("R", (x, y, z) => x == 2, i => new Vector3(0, 0, i), (x, y, z) => x, (x, y, z) => 2 - z, (x, y, z) => y),
            new FaceRotation("R’", (x, y, z) => x == 2, i => new Vector3(0, 0, -i), (x, y, z) => x, (x, y, z) => z, (x, y, z) => 2 - y),
            new FaceRotation("U", (x, y, z) => y == 0, i => new Vector3(0, i, 0), (x, y, z) => 2 - z, (x, y, z) => y, (x, y, z) => x),
            new FaceRotation("U’", (x, y, z) => y == 0, i => new Vector3(0, -i, 0), (x, y, z) => z, (x, y, z) => y, (x, y, z) => 2 - x),
            new FaceRotation("D", (x, y, z) => y == 2, i => new Vector3(0, -i, 0), (x, y, z) => z, (x, y, z) => y, (x, y, z) => 2 - x),
            new FaceRotation("D’", (x, y, z) => y == 2, i => new Vector3(0, i, 0), (x, y, z) => 2 - z, (x, y, z) => y, (x, y, z) => x));

        for (int i = 0; i < moves.Length; i++)
            moves[i].Reverse = moves[i ^ 1];

        _moves = moves.ToDictionary(f => f.Name, StringComparer.InvariantCultureIgnoreCase);
    }

    private float easeInOutQuad(float t, float b, float c, float d)
    {
        t /= d / 2;
        if (t < 1)
            return c / 2 * t * t + b;
        t--;
        return -c / 2 * (t * (t - 2) - 1) + b;
    }

    private float easeOutSine(float t, float b, float c, float d)
    {
        return (float) (c * Math.Sin(t / d * (Math.PI / 2)) + b);
    }

    IEnumerator ProcessTwitchCommand(string command)
    {
        if (_isSolved)
            yield break;

        if (command.Trim().Equals("reset", StringComparison.InvariantCultureIgnoreCase))
        {
            Reset.OnInteract();
            yield return new WaitForSeconds(.1f);
            yield break;
        }

        if (command.Trim().Equals("rotate", StringComparison.InvariantCultureIgnoreCase))
        {
            for (int i = 0; i <= 50; i += 5)
            {
                yield return Quaternion.Euler(easeInOutQuad(i, 0, 50, 50), 0, 0);
                yield return null;
            }
            for (int i = 0; i <= 360; i += 5)
            {
                yield return Quaternion.Euler(50, 0, 0) * Quaternion.Euler(0, easeInOutQuad(i, 0, 360, 360), 0);
                yield return null;
            }
            for (int i = 0; i <= 50; i += 5)
            {
                yield return Quaternion.Euler(easeInOutQuad(i, 50, -50, 50), 0, 0);
                yield return null;
            }
            yield break;
        }

        while (_queue.Count > 0)
        {
            yield return new WaitForSeconds(.1f);
            yield return "trycancel";
        }

        var rotations = new List<FaceRotation>();
        var cubelets = _cubelets;
        foreach (var cmd in command.ToLowerInvariant().Replace("'", "’").Split(new[] { ' ' }, StringSplitOptions.RemoveEmptyEntries))
        {
            int num = 1;
            FaceRotation rot;
            if (!_moves.TryGetValue(cmd, out rot) && cmd.Length == 2 && cmd.EndsWith("2"))
            {
                num = 2;
                _moves.TryGetValue(cmd.Substring(0, 1), out rot);
            }

            if (rot == null)
                yield break;

            for (int i = 0; i < num; i++)
            {
                cubelets = PerformRotationOnCubelets(cubelets, rot);
                rotations.Add(rot);

                if (isSolved(cubelets))
                {
                    yield return "solve";
                    goto perform;
                }
            }
        }

        perform:
        foreach (var rot in rotations)
        {
            _queue.Enqueue(rot);
            _performedMoves.Push(rot);
            Pushers[0].AddInteractionPunch();
            Audio.PlayGameSoundAtTransform(KMSoundOverride.SoundEffect.ButtonPress, Pushers[0].transform);
            yield return new WaitForSeconds(.25f);
        }
    }

    Transform[,,] PerformRotationOnCubelets(Transform[,,] cubelets, FaceRotation rot, bool setParent = false)
    {
        var newCubelets = new Transform[3, 3, 3];
        for (int x = 0; x < 3; x++)
            for (int y = 0; y < 3; y++)
                for (int z = 0; z < 3; z++)
                    if (x != 1 || y != 1 || z != 1)
                        if (rot.OnAxis(x, y, z))
                        {
                            if (setParent)
                                cubelets[x, y, z].parent = OnAxis;
                            newCubelets[x, y, z] = cubelets[rot.MapX(x, y, z), rot.MapY(x, y, z), rot.MapZ(x, y, z)];
                        }
                        else
                            newCubelets[x, y, z] = cubelets[x, y, z];
        return newCubelets;
    }

    IEnumerable PerformRotation(FaceRotation rot, int speed)
    {
        _cubelets = PerformRotationOnCubelets(_cubelets, rot, setParent: true);

        for (int i = speed; i <= 90; i += speed)
        {
            OnAxis.localEulerAngles = rot.Rotation(easeOutSine(i, 0, 90, 90));
            yield return null;
        }

        for (int x = 0; x < 3; x++)
            for (int y = 0; y < 3; y++)
                for (int z = 0; z < 3; z++)
                    if (x != 1 || y != 1 || z != 1)
                        _cubelets[x, y, z].parent = OffAxis;

        OnAxis.localEulerAngles = new Vector3(0, 0, 0);
    }
}
