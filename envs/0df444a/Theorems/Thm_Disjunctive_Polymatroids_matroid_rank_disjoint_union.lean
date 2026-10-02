-- Prove2me | Theorems.Thm_Disjunctive_Polymatroids_matroid_rank_disjoint_union
-- name    : Disjunctive.Polymatroids.matroid_rank_disjoint_union
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T17:12:30.037412+00:00
-- url     : https://prove2.me/theorems/15c9c9c4-0944-40dc-bbaf-88c52f21c58b
-- title:
--   Proposition 13.16 — the matroid-rank-function specialization
-- statement:
--   This is Proposition 13.16 of Balas's *Disjunctive Programming*: a closed-form convex hull for
--   the disjoint-space union of two Application-1 polytopes, generalizing an earlier
--   matroid-specific result.
--
--   For set functions $r_1,r_2$ satisfying conditions 1-3 of Application 1 (on ground sets $M,N$
--   respectively),
--   $$
--   \mathrm{conv}(Z(r_1,r_2)) = \Big\{(x,y)\in[0,1]^m\times[0,1]^n :
--   \frac{|A|-x(A)}{|A|-r_1(A)} + \frac{|B|-y(B)}{|B|-r_2(B)} \ge 1 \ \ \forall A\subseteq M,
--   B\subseteq N \text{ with } r_1(A)<|A|,\ r_2(B)<|B|\Big\}.
--   $$
--
--   The book derives this via the complement polytope $C(r) := \{w\in[0,1]^n : e-w\in P(r)\}$ and
--   Theorem 13.13's general dominant formula for a union of two upper monotone polytopes, applied
--   to $C(r_1)\times[0,1]^n \cup [0,1]^m\times C(r_2)$, then complementing back. For matroid rank
--   functions (satisfying 1-3, integer-valued and submodular), this characterization was obtained
--   earlier by different means; the present result is strictly more general (e.g. it holds for a
--   rank function of an intersection of two matroids).
--
--   **Formalization Note.** `ZDisjoint`/`PolymatroidP` restate the book's `Z(r₁,r₂)`/`P(r)`
--   directly; the theorem is stated for `IsApp1SetFunction` (not `IsPolymatroidRankFunction`),
--   matching the proposition's own hypothesis exactly ("set functions on N... satisfying 1-3 in
--   our Application 1"), which is broader than requiring submodularity.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 224-225, Proposition 13.16

import Mathlib
import Definitions.Def_Disjunctive_Polymatroids_Basic

namespace Disjunctive.Polymatroids

/-- Proposition 13.16 (Balas §13.4, p. 224-225): for set functions `r₁,r₂` satisfying conditions
1-3 of Application 1, `conv(Z(r₁,r₂)) = {(x,y) : (|A|-x(A))/(|A|-r₁(A)) + (|B|-y(B))/(|B|-r₂(B))
≥1 for all A⊆M, B⊆N with r₁(A)<|A|, r₂(B)<|B|}`. -/
theorem matroid_rank_disjoint_union {m n : ℕ} (r1 : Finset (Fin m) → ℝ)
    (r2 : Finset (Fin n) → ℝ) (hr1 : IsApp1SetFunction r1) (hr2 : IsApp1SetFunction r2) :
    convexHull ℝ (ZDisjoint r1 r2) =
      {p : (Fin m → ℝ) × (Fin n → ℝ) | (∀ i, 0 ≤ p.1 i ∧ p.1 i ≤ 1) ∧
        (∀ j, 0 ≤ p.2 j ∧ p.2 j ≤ 1) ∧
        ∀ A : Finset (Fin m), ∀ B : Finset (Fin n), r1 A < A.card → r2 B < B.card →
          1 ≤ ((A.card : ℝ) - SumOver p.1 A) / ((A.card : ℝ) - r1 A) +
            ((B.card : ℝ) - SumOver p.2 B) / ((B.card : ℝ) - r2 B)} := by sorry

end Disjunctive.Polymatroids
