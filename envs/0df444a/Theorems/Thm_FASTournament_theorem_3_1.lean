-- Prove2me | Theorems.Thm_FASTournament_theorem_3_1
-- name    : FASTournament.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:34:59.941638+00:00
-- url     : https://prove2.me/theorems/4dab130e-68f3-481f-9d84-9873d95fcfa8
-- title:
--   Theorem 3.1 — Möbius-free strong tournaments other than $F_1$, $G_1$ are FAS Mengerian
-- statement:
--   Let $T=(V,A)$ be a Möbius-free strong tournament with $|V|\ge 3$ and $T\notin\{F_1,G_1\}$. Then $T$ is FAS Mengerian.
--
--   Together with Lemma 4.1 ($G_1$), the case of $F_1$, and the reduction to strong tournaments, it gives implication (i) ⇒ (iii) of Theorem 1.2.
--
--   Differences from the source:
--   - encoding: a tournament T = (V, A) (finite) → T : Digraph V on a Fintype V with IsTournament T (no loops; exactly one of u → v, v → u for u ≠ v); reason: the same objects; Mathlib's Digraph allows loops and 2-cycles, which the predicate excludes
--   - encoding: contains … as a subgraph → ContainsSubgraph: an injective vertex map sending every arc of the ladder to an arc of T (not necessarily induced); reason: the usual meaning of subgraph; the ladders are drawn on vertices u1, …, uk, taken as Fin k with index i − 1
--   - encoding: T other than F1 and G1 / T ∉ {F1, G1} → ¬ Isomorphic T F1 ∧ ¬ Isomorphic T G1; reason: T has an arbitrary vertex set, so membership is up to isomorphism
--   - encoding: F1 of Figure 4 → F1 := the subdigraph of G1 induced by vertices 1, …, 5 (G1 − v6, p.26); reason: the paper states that F1 arises from G1 by deleting v6; G1 − v6 is the regular 5-tournament drawn in Figure 4
--   - encoding: TDI: for every nonnegative integral w for which the optimum is finite, the dual maximum has an integral optimal solution → IsTDI: for every integral w for which the real primal LP is feasible and bounded below, some integral dual-feasible y has objective at least that of every real dual-feasible vector; reason: for the nonnegative incidence matrices a cost with a negative entry makes the primal infeasible or unbounded, and by LP duality a finite primal optimum means an attained dual maximum; same notion
--   - encoding: N, the FAS-arc incidence matrix (rows: FASs) → rows indexed by all FASs F of G as finite arc sets; entry 1 if e ∈ F, else 0; reason: the same matrix up to the order of its rows
--   - encoding: cycle (directed) → IsDirCycle: the arc set of a closed walk through k ≥ 2 distinct vertices; reason: a cycle is determined by its arc set, which is how it enters the incidence matrices; loops are not cycles, and tournaments have none
-- source:
--   Chen, Ding, Zang & Zhao, Packing Feedback Arc Sets in Tournaments Exactly, Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, Theorem 3.1, p.12

import Mathlib
import Definitions.Def_FASTournament_IsTournament
import Definitions.Def_FASTournament_IsStrong
import Definitions.Def_FASTournament_Isomorphic
import Definitions.Def_FASTournament_F1
import Definitions.Def_FASTournament_G1
import Definitions.Def_FASTournament_MobiusFree
import Definitions.Def_FASTournament_FASMengerian

namespace FASTournament

/-- **Theorem 3.1.**
Chen, Ding, Zang & Zhao, *Packing Feedback Arc Sets in Tournaments Exactly*,
Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, Theorem 3.1, p.12: "Let T = (V, A) be a Möbius-free strong tournament with |V| ≥ 3 and
T ∉ {F1, G1}. Then T is FAS Mengerian."

**Formalization Note.** "T ∉ {F₁, G₁}" is read up to isomorphism. -/
theorem theorem_3_1 {V : Type*} [Fintype V] (T : Digraph V) (hT : IsTournament T)
    (hM : MobiusFree T) (hs : IsStrong T) (hV : 3 ≤ Fintype.card V) (hF1 : ¬ Isomorphic T F1)
    (hG1 : ¬ Isomorphic T G1) : FASMengerian T := by sorry

end FASTournament
