-- Prove2me | Theorems.Thm_Disjunctive_ConvexHull_extreme_point_correspondence
-- name    : Disjunctive.ConvexHull.extreme_point_correspondence
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T16:11:01.81899+00:00
-- url     : https://prove2.me/theorems/64ed3fc3-e53a-4922-831f-faac479ff9a1
-- title:
--   Corollary 2.2 — the extreme-point correspondence
-- statement:
--   This is Corollary 2.2 of Balas's *Disjunctive Programming*, an immediate structural
--   consequence of Theorem 2.1's construction: it pins down exactly which points of the lifted
--   polyhedron $P$ are its extreme points, in terms of the extreme points of $\mathrm{cl\,conv}(F)$.
--
--   Using the notation of Theorem 2.1 ($F$, $Q^*$, $P_h$, and the lifted polyhedron $P$ of
--   tuples $(x, \{y^h\}, \{y^h_0\})$):
--
--   1. If $x^*$ is an extreme point of $\mathrm{cl\,conv}(F)$, then the tuple with $x = x^*$,
--      $(y^k, y^k_0) = (x^*, 1)$ for some $k \in Q^*$, and $(y^h, y^h_0) = (0,0)$ for every other
--      $h$, is an extreme point of $P$.
--   2. Conversely, if a tuple $(\bar x, \{y^h\}, \{y^h_0\})$ is an extreme point of $P$, then
--      $y^k = \bar x$ and $y^k_0 = 1$ for some $k \in Q^*$, $(y^h, y^h_0) = (0,0)$ for every other
--      $h$, and $\bar x$ is an extreme point of $\mathrm{cl\,conv}(F)$.
--
--   So the extreme points of $P$ are exactly the "one-hot" tuples built from an extreme point of
--   $\mathrm{cl\,conv}(F)$ by placing it entirely on a single disjunct's coordinates and zeroing
--   every other disjunct's coordinates — a strong structural constraint on what the lifting can
--   produce, and the key fact that makes the lifted polyhedron $P$ a faithful vertex-preserving
--   representation of $\mathrm{cl\,conv}(F)$ rather than merely a set with the same projection.
--
--   **Formalization Note.** `Set.extremePoints ℝ S` is Mathlib's extreme-point set. Both
--   directions are stated with the disjunct index $k$ existentially quantified, since the book's
--   correspondence names $k$ but does not claim it is computable from $x^*$ alone without
--   reference to the tuple.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 19-20, Corollary 2.2

import Mathlib
import Definitions.Def_Disjunctive_ConvexHull_Polyhedra
import Definitions.Def_Disjunctive_ConvexHull_LiftedPolyhedron

namespace Disjunctive.ConvexHull

/-- Corollary 2.2 (Balas §2.1, p. 19-20): the extreme points of `cl conv F` correspond exactly
to the "one active term, rest zero" extreme points of the lifted polyhedron `P`. -/
theorem extreme_point_correspondence {n : ℕ} {Q : Type*} [Fintype Q] (m : Q → ℕ)
    (A : (h : Q) → Matrix (Fin (m h)) (Fin n) ℝ) (b : (h : Q) → Fin (m h) → ℝ) :
    (∀ xstar ∈ Set.extremePoints ℝ (closure (convexHull ℝ (DisjunctiveSet m A b))),
      ∃ k ∈ FeasibleIndices m A b, ∃ y : Q → Fin n → ℝ, ∃ y0 : Q → ℝ,
        (xstar, (y, y0)) ∈ Set.extremePoints ℝ (LiftedPolyhedron m A b (FeasibleIndices m A b)) ∧
        y k = xstar ∧ y0 k = 1 ∧ ∀ h, h ≠ k → y h = 0 ∧ y0 h = 0)
    ∧
    (∀ (xbar : Fin n → ℝ) (y : Q → Fin n → ℝ) (y0 : Q → ℝ),
      (xbar, (y, y0)) ∈ Set.extremePoints ℝ (LiftedPolyhedron m A b (FeasibleIndices m A b)) →
      ∃ k ∈ FeasibleIndices m A b, y k = xbar ∧ y0 k = 1 ∧ (∀ h, h ≠ k → y h = 0 ∧ y0 h = 0) ∧
        xbar ∈ Set.extremePoints ℝ (closure (convexHull ℝ (DisjunctiveSet m A b)))) := by sorry

end Disjunctive.ConvexHull
