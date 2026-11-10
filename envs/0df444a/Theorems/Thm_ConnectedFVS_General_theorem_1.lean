-- Prove2me | Theorems.Thm_ConnectedFVS_General_theorem_1
-- name    : ConnectedFVS.General.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T17:18:25.252006+00:00
-- url     : https://prove2.me/theorems/299c7a8a-ec40-40cb-8b2d-7fb4af59f241
-- title:
--   Theorem 1 — Single-exponential connected feedback vertex set on general graphs
-- statement:
--   There are one deterministic finite program $M$, an absolute constant $c>1$, a positive constant $C$ and a natural exponent $d$, all independent of the instance, such that for every finite simple undirected graph $G$ and natural budget $k$, including zero, $M$ decides whether a vertex set $F$ exists with $|F|\le k$, acyclic induced complement $G[V\setminus F]$, and connected induced graph $G[F]$. If $N$ is the encoding length, its actual halting time satisfies
--
--   $$T\le C\,c^k(N+1)^d.$$
--
--   The program accepts exactly the yes-instances and rejects every no-instance. Graphs may be empty or disconnected. Connectedness of $G[F]$ includes nonemptiness. No polynomial-space guarantee is added to this result.
--
--   Differences from the source:
--   - encoding: finite graphs with named vertices → vertices Fin n with explicit Boolean adjacency and membership matrices; reason: every finite input has a relabeling; no graph-class restriction is imposed
--   - encoding: input size n → self-delimiting adjacency-matrix input of length N including the binary natural budget k; reason: an explicit polynomial-size encoding preserves every finite graph instance, including budgets larger than the graph
--   - encoding: a deterministic algorithm with asymptotic resource bounds → one finite ordinary binary-stack program with globally quantified positive natural constants and exponents, exact step counts, and bounds using (N+1); reason: finite alphabets exclude unit-cost unbounded data; fixed-machine simulations and per-instance polynomial arithmetic costs preserve the claimed exponential base
--   - encoding: some constant c in a single-exponential bound → a natural base c greater than 1; reason: rounding a real base upwards to an integer greater than 1 gives the same existential asymptotic class
--   - reading: connected induced selected graph with no explicit null-graph convention → Connected includes nonemptiness; reason: fixes the brief's ordinary nonempty-connected interpretation without assuming that the input graph is nonempty
--   - generalization: positive parameter k in the introduction → natural k including zero, with zero rejected under nonempty connectivity; reason: all positive source instances are preserved; the extra boundary is decidable immediately and is compatible with the natural parameter convention of Section 2
-- source:
--   Misra et al., FPT-Algorithms for Connected Feedback Vertex Set, arXiv:0909.3180v1 (17 September 2009), Theorem 1, PDF p. 6

import Definitions.Def_ConnectedFVS_General_BinaryMachine
import Definitions.Def_ConnectedFVS_General_Encodings

namespace ConnectedFVS.General

theorem theorem_1 :
    ∃ (M : BinaryMachine) (c C d : ℕ), 1 < c ∧ 0 < C ∧
      M.Decides cfvsLanguage ∧ ∀ I : CFVSInstance,
        M.TimeBounded I.encode (C * c ^ I.k * (I.encode.length + 1) ^ d) := by sorry

end ConnectedFVS.General
