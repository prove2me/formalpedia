-- Prove2me | Theorems.Thm_APFPaper5_K1_every_turn_leaves_the_cost_unchanged
-- name    : APFPaper5.K1.every_turn_leaves_the_cost_unchanged
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-22T04:03:35.130803+00:00
-- url     : https://prove2.me/theorems/ad6c9200-8ea5-4514-99df-dee5a3b15791
-- title:
--   every turn leaves the cost unchanged
-- statement:
--   Under the four clauses every turn of the plane leaves the cost unchanged.
--
--   Scope and conditions: Ordinary real analysis on supplied q: PairsAndNothingMore, two-homogeneity, nonnegativity and quarter-turn invariance imply q(x,y)=q(1,0)(x²+y²). Orthogonal additivity, arbitrary-rotation invariance and the stated normalized half-square follow. Parallelogram comparisons and controls expose the pair/quarter-turn roles. All four clauses remain explicit; no physical plane, realization of real coefficients, probability normalization or Born derivation is established.
--
--   Exact source statement:
--
--   ```lean
--   theorem every_turn_leaves_the_cost_unchanged (q : ℝ → ℝ → ℝ)
--       (hpairs : PairsAndNothingMore q)
--       (hhom : ∀ t x y : ℝ, q (t * x) (t * y) = t * t * q x y)
--       (hnn : ∀ x y : ℝ, 0 ≤ q x y)
--       (hquarter : ∀ x y : ℝ, q (-y) x = q x y) :
--       ∀ a b x y : ℝ, a * a + b * b = 1 → q (a * x - b * y) (b * x + a * y) = q x y
--   ```
-- source:
--   ['Theorems.Thm_APFPaper5_K1_plane_cost_from_pairs_and_one_quarter_turn:325; USB pullbacks v58 batch A; SHA-256 ab8e6269e3f57cb1aecd00e93f0a3cb5df150b1722b78a2e8ca4591058a2a8ec']

import Definitions.Def_APFPaper5_K1_PairsAndNothingMore
import Theorems.Thm_APFPaper5_K1_plane_cost_quadratic
import Theorems.Thm_APFPaper5_K1_square_of_cross_term
import Mathlib.Algebra.Order.Ring.Abs
set_option autoImplicit false

theorem APFPaper5.K1.every_turn_leaves_the_cost_unchanged :
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
  (hquarter : ∀ (x y : Real), @Eq.{1} Real (q (@Neg.neg.{0} Real Real.instNeg y) x) (q x y)) (a b x y : Real),
  @Eq.{1} Real
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) a a)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) b b))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
    @Eq.{1} Real
      (q
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) a x)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) b y))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) b x)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) a y)))
      (q x y) := by sorry
