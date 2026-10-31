-- Prove2me | Theorems.Thm_FASTournament_theorem_2_7
-- name    : FASTournament.theorem_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:33:13.638044+00:00
-- url     : https://prove2.me/theorems/cfe6adae-49d5-4785-8362-e828309db789
-- title:
--   Theorem 2.7 — a strong tournament other than $F_1$, $G_1$ is Möbius-free iff it lies in $\mathcal P$ (corrected: $|V|\ge 3$)
-- statement:
--   Let $T=(V,A)$ be a strong tournament with $|V|\ge 3$ that is isomorphic to neither $F_1$ nor $G_1$. Then $T$ is Möbius-free if and only if $T\in\mathcal P$, i.e. $T$ has the global structure of Figure 7: a chain of vertical blocks $A_1,\dots,A_m$ ($m\ge 1$), each in $\mathcal Q$ centered at a join vertex $v_i$, linked by horizontal blocks $B_1,\dots,B_{m-1}$ of the three shapes of Figure 7, with all other arcs directed from left to right, $v_1$ having an out-neighbor in the leftmost building block of $A_1$ and $v_m$ an in-neighbor in the rightmost building block of $A_m$.
--
--   This global description of Möbius-free strong tournaments is the structural input of the induction in Theorem 3.1.
--
--   Differences from the source:
--   - encoding: a tournament T = (V, A) (finite) → T : Digraph V on a Fintype V with IsTournament T (no loops; exactly one of u → v, v → u for u ≠ v); reason: the same objects; Mathlib's Digraph allows loops and 2-cycles, which the predicate excludes
--   - encoding: contains … as a subgraph → ContainsSubgraph: an injective vertex map sending every arc of the ladder to an arc of T (not necessarily induced); reason: the usual meaning of subgraph; the ladders are drawn on vertices u1, …, uk, taken as Fin k with index i − 1
--   - encoding: T other than F1 and G1 / T ∉ {F1, G1} → ¬ Isomorphic T F1 ∧ ¬ Isomorphic T G1; reason: T has an arbitrary vertex set, so membership is up to isomorphism
--   - encoding: F1 of Figure 4 → F1 := the subdigraph of G1 induced by vertices 1, …, 5 (G1 − v6, p.26); reason: the paper states that F1 arises from G1 by deleting v6; G1 − v6 is the regular 5-tournament drawn in Figure 4
--   - correction: T a strong tournament other than F1 and G1 (no bound on |V|) → additional hypothesis 3 ≤ Fintype.card V; reason: the one-vertex tournament is strong (vacuously) and Möbius-free but not in P, since A1 = {v1} has no leftmost building block for v1 to have an out-neighbor in; there is no strong tournament on two vertices, so |V| ≥ 3 excludes exactly this case
--   - reading: "v1 has an out-neighbor in the leftmost building block of A1, and vm has an in-neighbor in the rightmost building block of Am" → existential: the leftmost (rightmost) building block exists and contains such a neighbor, so n1 ≥ 1 and nm ≥ 1; reason: the proof uses the existence (claim (1), p.10, |A1| ≥ 2) and re-establishes it at the end of the "only if" part (p.12)
--   - encoding: the description of Figure 7 (blocks A_i, B_i, join vertices, building blocks, "left to right") → InP: a group index g : V → {0, …, 2m − 2} (A_i = g⁻¹(2i), B_i = g⁻¹(2i+1) ∪ {v_i, v_{i+1}}), positions pos in the building blocks, 0-based indices; reason: the same structures; "all other arcs" are the pairs lying in no common block
-- source:
--   Chen, Ding, Zang & Zhao, Packing Feedback Arc Sets in Tournaments Exactly, Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, Theorem 2.7, Figure 7 and the paragraph after it, p.8

import Mathlib
import Definitions.Def_FASTournament_IsTournament
import Definitions.Def_FASTournament_IsStrong
import Definitions.Def_FASTournament_Isomorphic
import Definitions.Def_FASTournament_F1
import Definitions.Def_FASTournament_G1
import Definitions.Def_FASTournament_MobiusFree
import Definitions.Def_FASTournament_InP

namespace FASTournament

/-- **Theorem 2.7 (corrected: `|V| ≥ 3`).**
Chen, Ding, Zang & Zhao, *Packing Feedback Arc Sets in Tournaments Exactly*,
Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, Theorem 2.7, p.8: "Let T = (V, A) be a strong tournament other than F1 and G1. Then T is
Möbius-free iff it satisfies the following description:" (Figure 7 and the paragraph after it;
the class of such tournaments is `𝒫`, `InP`).

For every strong tournament `T` with at least three vertices that is isomorphic to neither `F₁`
nor `G₁`: `T` is Möbius-free iff `T ∈ 𝒫`.

**Formalization Note.** The hypothesis `3 ≤ |V|` corrects the printed statement: the one-vertex
tournament is strong and Möbius-free but not in `𝒫` (its `A₁ = {v₁}` has no leftmost building
block). There is no strong tournament on two vertices. "Other than F₁ and G₁" is read up to
isomorphism. -/
theorem theorem_2_7 {V : Type*} [Fintype V] (T : Digraph V) (hT : IsTournament T)
    (hs : IsStrong T) (hV : 3 ≤ Fintype.card V) (hF1 : ¬ Isomorphic T F1)
    (hG1 : ¬ Isomorphic T G1) :
    MobiusFree T ↔ InP T := by sorry

end FASTournament
