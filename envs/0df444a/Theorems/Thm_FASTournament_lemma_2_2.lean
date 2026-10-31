-- Prove2me | Theorems.Thm_FASTournament_lemma_2_2
-- name    : FASTournament.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:32:36.584602+00:00
-- url     : https://prove2.me/theorems/42a844e0-e8c9-45a6-bf7b-34ce1846014b
-- title:
--   Lemma 2.2 — a strong 1-sum is Möbius-free iff both summands are
-- statement:
--   Suppose a strong tournament $T$ is a 1-sum of two tournaments $T_1$ and $T_2$. Then $T$ is Möbius-free if and only if both $T_1$ and $T_2$ are Möbius-free.
--
--   So Möbius-freeness is closed under taking 1-sums, which is how Lemma 2.11 and Theorem 2.7 build Möbius-free tournaments from small pieces.
--
--   Differences from the source:
--   - encoding: a tournament T = (V, A) (finite) → T : Digraph V on a Fintype V with IsTournament T (no loops; exactly one of u → v, v → u for u ≠ v); reason: the same objects; Mathlib's Digraph allows loops and 2-cycles, which the predicate excludes
--   - encoding: contains … as a subgraph → ContainsSubgraph: an injective vertex map sending every arc of the ladder to an arc of T (not necessarily induced); reason: the usual meaning of subgraph; the ladders are drawn on vertices u1, …, uk, taken as Fin k with index i − 1
--   - encoding: T is a 1-sum of T1 and T2 (p.5) → IsOneSum T T1 T2: T1, T2 tournaments with ≥ 3 vertices, arcs a1 → b1 with d⁺(a1) = 1 and b2 → a2 with d⁻(a2) = 1, and T isomorphic to the 1-sum construction; reason: the definition of p.5, with T taken up to isomorphism since it has its own vertex set
-- source:
--   Chen, Ding, Zang & Zhao, Packing Feedback Arc Sets in Tournaments Exactly, Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, Lemma 2.2, p.6

import Mathlib
import Definitions.Def_FASTournament_IsTournament
import Definitions.Def_FASTournament_IsStrong
import Definitions.Def_FASTournament_IsOneSum
import Definitions.Def_FASTournament_MobiusFree

namespace FASTournament

/-- **Lemma 2.2.**
Chen, Ding, Zang & Zhao, *Packing Feedback Arc Sets in Tournaments Exactly*,
Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, Lemma 2.2, p.6: "Suppose a strong tournament T is a 1-sum of two tournaments T1 and T2.
Then T is Möbius-free iff both T1 and T2 are Möbius-free."

**Formalization Note.** `IsOneSum T T₁ T₂` includes that `T₁, T₂` are tournaments with at least
three vertices and the special-arc conditions of p.5. -/
theorem lemma_2_2 {V V₁ V₂ : Type*} [Fintype V] (T : Digraph V) (T₁ : Digraph V₁)
    (T₂ : Digraph V₂) (hT : IsTournament T) (hs : IsStrong T) (h : IsOneSum T T₁ T₂) :
    MobiusFree T ↔ MobiusFree T₁ ∧ MobiusFree T₂ := by sorry

end FASTournament
