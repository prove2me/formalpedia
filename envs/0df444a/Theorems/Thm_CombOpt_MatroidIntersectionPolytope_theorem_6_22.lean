-- Prove2me | Theorems.Thm_CombOpt_MatroidIntersectionPolytope_theorem_6_22
-- name    : CombOpt.MatroidIntersectionPolytope.theorem_6_22
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:41:47.415985+00:00
-- url     : https://prove2.me/theorems/c1b47a43-5ec7-42d0-aeb3-c098afc871ea
-- title:
--   Theorem 6.22 — a rational polytope is integral iff all integral objectives have integral optimal values
-- statement:
--   Let $P\subseteq\mathbb R^n$ be a rational polytope. Then $P$ is integral if and only if, for every integral vector $w$, the optimal value of
--
--   $$
--   \max\{w^Tx : x\in P\}
--   $$
--
--   is an integer.
--
--   This characterization (Hoffman, 1974) lets one prove integrality of a polytope from the integrality of optimal objective values alone; it is the step from total dual integrality to integrality in Theorem 6.29.
--
--   **Formalization Note** The right-hand side is written as: whenever $x\in P$ maximizes $w^Tx$ over $P$, the value $w^Tx$ is an integer. For a nonempty polytope a maximizer exists, so this is the book's condition.
--
--   Differences from the source:
--   - encoding: P ⊆ ℝⁿ → P ⊆ ℝ^n with coordinates indexed by an arbitrary finite type n; reason: any finite type is in bijection with {1, …, n}; same instances up to relabelling coordinates
--   - reading: the optimal value of max{wᵀx : x ∈ P} is an integer → every maximizer x of wᵀx over P has wᵀx ∈ ℤ; reason: identical for nonempty P (a maximizer exists on a nonempty polytope); for P = ∅ the book's optimal value is undefined and both sides of the Lean statement hold
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §6.4, Theorem 6.22, p. 219 (PDF p. 227)

import Mathlib
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_polyhedron
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_IsRationalPolytope
import Definitions.Def_CombOpt_MatchingPolytope_IsFace
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_IsIntegralPolyhedron

namespace CombOpt.MatroidIntersectionPolytope

/-- **Theorem 6.22** (Hoffman 1974).
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §6.4, Theorem 6.22, p. 219 (PDF p. 227): "A rational polytope P is integral if and only if
for all integral vectors w the optimal value of max{wᵀx : x ∈ P} is an integer."

For a rational polytope `P ⊆ ℝⁿ`: `P` is integral if and only if, for every integral `w`, every
optimal value of `max {wᵀx : x ∈ P}` is an integer (i.e. whenever `x ∈ P` maximizes `wᵀx` over
`P`, `wᵀx ∈ ℤ`).

**Formalization Note.** The right-hand side is stated for every maximizer; for a nonempty
polytope a maximizer exists, so this is the book's condition. For `P = ∅` both sides hold. -/
theorem theorem_6_22 {n : Type*} [Fintype n] (P : Set (n → ℝ)) (hP : IsRationalPolytope P) :
    IsIntegralPolyhedron P ↔
      ∀ w : n → ℤ, ∀ x ∈ P, (∀ x' ∈ P, ∑ j, (w j : ℝ) * x' j ≤ ∑ j, (w j : ℝ) * x j) →
        ∃ k : ℤ, ∑ j, (w j : ℝ) * x j = k := by sorry

end CombOpt.MatroidIntersectionPolytope
