-- Prove2me | Theorems.Thm_CutRankSched_Supplement_theorem_7_1
-- name    : CutRankSched.Supplement.theorem_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:55:43.260079+00:00
-- url     : https://prove2.me/theorems/97f3503c-363b-4740-af1f-a986eb89564d
-- title:
--   Theorem 7.1 — all-commuting coloring embedding
-- statement:
--   There is one construction $G\mapsto f(G)$, computable in polynomial time, from finite simple graphs to scheduling instances: one machine and one constant $C$ compute the encoding of $f(G)$ from the encoding of $G$ within $C(N+1)^C$ steps, for every graph $G$ on $V=\{0,\dots,N-1\}$. For every such $G$, with $E$ its edge set, the instance $f(G)$
--
--   1. has $n=|V|$ events and $m=|V|+|E|$ qubits;
--   2. has $A=0$, $r=\mathrm{rank}\,A=0$ and $\kappa_\pi=0$;
--   3. has $X^\circ\cong G$, the isomorphism being the identity on events and vertices;
--   4. is valid: every Pauli support is nonempty and every exposure region is connected;
--   5. preserves the vertex-separation width: $w^\circ(f(G))=\mathrm{vsw}(G)$ in the order of the numbering;
--   6. for every integer $q\ge1$, has a feasible schedule of at most $q$ rounds if and only if $G$ is $q$-colorable.
--
--   Even the all-commuting special case of the scheduling problem thus contains graph coloring, which gives NP-hardness for $L=3$ (Corollary 7.2).
--
--   **Formalization Note** The ordering of $V$ is the numbering of $\{0,\dots,N-1\}$; every ordering is covered by renumbering $G$.
--
--   Differences from the source:
--   - reading: one can construct in polynomial time → one machine and one constant C with FasterPrimeEnum.RunsWithin M out (encGraph G) (encInstance (f G)) (C(N+1)^C); reason: the paper names no machine model; the published SubexponentialSAT model of the base goal
--   - generalization: given G and an integer q ≥ 1, construct an instance → one instance f G for all q ≥ 1 simultaneously; reason: the source's construction does not use q; fixing q gives the source's claim
--   - reading: for any ordering of V, the corresponding event ordering preserves its vertex-separation width → width (f G) = vsw G for every graph G on Fin N, the numbering being the ordering; reason: every ordering of V is a renumbering of G, and f applies to every numbered graph
--   - encoding: X° ≅ G, |V|, |E| → Residual (f G) i j ↔ G.Adj i j via Fin.cast, |E| = G.edgeSet.ncard; reason: the identity isomorphism; same graphs
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Theorem 7.1, p.14

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_Instance_Valid
import Definitions.Def_CutRankSched_A
import Definitions.Def_CutRankSched_Residual
import Definitions.Def_CutRankSched_Feasible
import Definitions.Def_CutRankSched_width
import Definitions.Def_CutRankSched_cutRank
import Definitions.Def_CutRankSched_encInstance
import Definitions.Def_CutRankSched_Supplement_encGraph
import Definitions.Def_CutRankSched_Supplement_vsw
import Definitions.Def_FasterPrimeEnum_RunsWithin

set_option autoImplicit false

open OAI.Algorithms.SubexponentialSAT.Computation

namespace CutRankSched

namespace Supplement

/-- **Theorem 7.1 (All-commuting coloring embedding)** (Zhao et al., *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), Theorem 7.1, p.14). Given any finite
simple graph `G = (V, E)` and integer `q ≥ 1`, one can construct in polynomial time a fixed-event
conservative scheduling instance with `n = |V|`, `m = |V| + |E|`, `A = 0`, `r = κ_π = 0`,
`X° ≅ G`, such that the instance has a feasible schedule of at most `q` rounds iff `G` is
`q`-colorable. Every Pauli support is nonempty and every exposure region is connected. For any
ordering of `V`, the corresponding event ordering preserves its vertex-separation width exactly.

Stated as: one construction `f` (independent of `q`) and one machine computing `encInstance (f G)`
from `encGraph G` within `C(N+1)^C` steps; for every `G` on `V = {0, …, N−1}`, `f G` has `n = N`
events, `m = N + |E|` qubits, `A = 0`, `rank A = 0`, `κ_π = 0`, residual edges exactly the edges of
`G` (the isomorphism is the identity), is valid, has width `vsw(G)`, and for every `q ≥ 1` is
feasible in `q` rounds iff `G` is `q`-colorable.

**Formalization Note** The ordering of `V` is the numbering of `Fin N`; every ordering is covered by
relabelling `G`. `Fin.cast` transports events to vertices. "Computes in time" is the published
`FasterPrimeEnum.RunsWithin` (same `SubexponentialSAT` machine model: halts within the bound with
exactly the output word on tape `out`). -/
theorem theorem_7_1 :
    ∃ f : (N : ℕ) → SimpleGraph (Fin N) → Instance,
      (∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (C : ℕ), ∀ (N : ℕ) (G : SimpleGraph (Fin N)),
        FasterPrimeEnum.RunsWithin M out (encGraph G) (encInstance (f N G))
          ((C * (N + 1) ^ C : ℕ) : ℝ)) ∧
      ∀ (N : ℕ) (G : SimpleGraph (Fin N)), ∃ hn : (f N G).n = N,
        (f N G).m = N + G.edgeSet.ncard ∧ A (f N G) = 0 ∧ (A (f N G)).rank = 0 ∧
        cutRank (f N G) = 0 ∧
        (∀ i j : Fin (f N G).n, Residual (f N G) i j ↔ G.Adj (Fin.cast hn i) (Fin.cast hn j)) ∧
        (f N G).Valid ∧ width (f N G) = vsw G ∧
        ∀ q : ℕ, 1 ≤ q → (Feasible (f N G) q ↔ G.Colorable q) := by sorry

end Supplement

end CutRankSched
