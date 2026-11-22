-- Prove2me | Theorems.Thm_APFPaper5_K1_the_cost_adds_across_perpendicular_directions
-- name    : APFPaper5.K1.the_cost_adds_across_perpendicular_directions
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-22T06:53:47.7768+00:00
-- url     : https://prove2.me/theorems/fa43f3ca-af43-4469-ac6f-991a1f2dce71
-- title:
--   the cost adds across perpendicular directions
-- statement:
--   Under the four clauses the cost adds across perpendicular directions.
--
--   Scope and conditions: Ordinary real analysis on supplied q: PairsAndNothingMore, two-homogeneity, nonnegativity and quarter-turn invariance imply q(x,y)=q(1,0)(x²+y²). Orthogonal additivity, arbitrary-rotation invariance and the stated normalized half-square follow. Parallelogram comparisons and controls expose the pair/quarter-turn roles. All four clauses remain explicit; no physical plane, realization of real coefficients, probability normalization or Born derivation is established.
--
--   Exact source statement:
--
--   ```lean
--   theorem the_cost_adds_across_perpendicular_directions (q : ℝ → ℝ → ℝ)
--       (hpairs : PairsAndNothingMore q)
--       (hhom : ∀ t x y : ℝ, q (t * x) (t * y) = t * t * q x y)
--       (hnn : ∀ x y : ℝ, 0 ≤ q x y)
--       (hquarter : ∀ x y : ℝ, q (-y) x = q x y) :
--       ∀ x1 y1 x2 y2 : ℝ, x1 * x2 + y1 * y2 = 0 →
--         q (x1 + x2) (y1 + y2) = q x1 y1 + q x2 y2
--   ```
-- source:
--   ['Theorems.Thm_APFPaper5_K1_plane_cost_from_pairs_and_one_quarter_turn:309; USB pullbacks v58 batch A; SHA-256 ab8e6269e3f57cb1aecd00e93f0a3cb5df150b1722b78a2e8ca4591058a2a8ec']

import Definitions.Def_APFPaper5_K1_PairsAndNothingMore
import Theorems.Thm_APFPaper5_K1_plane_cost_quadratic
import Theorems.Thm_APFPaper5_K1_square_of_cross_term
import Mathlib.Algebra.Order.Ring.Abs
set_option autoImplicit false

theorem APFPaper5.K1.the_cost_adds_across_perpendicular_directions :
∀ (q : Real → Real → Real) (hpairs : APFPaper5.K1.PairsAndNothingMore q)
  (hhom :
    ∀ (t x y : Real),
      @Eq.{1} Real
        (q (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) t x)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) t y))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) t t) (q x y)))
  (hnn :
    ∀ (x y : Real),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (q x y))
  (hquarter : ∀ (x y : Real), @Eq.{1} Real (q (@Neg.neg.{0} Real Real.instNeg y) x) (q x y)) (x1 y1 x2 y2 : Real),
  @Eq.{1} Real
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) x1 x2)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) y1 y2))
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
    @Eq.{1} Real
      (q (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) x1 x2)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) y1 y2))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (q x1 y1) (q x2 y2)) := by sorry
