-- Prove2me | Theorems.Thm_APFPaper5_K1_cross_term_from_pairs_and_one_quarter_turn
-- name    : APFPaper5.K1.cross_term_from_pairs_and_one_quarter_turn
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-22T04:03:05.250303+00:00
-- url     : https://prove2.me/theorems/2152834c-0b6f-437c-b6eb-efed59febc7d
-- title:
--   cross term from pairs and one quarter turn
-- statement:
--   Under the four clauses the cost of the unit direction and (u, v) together exceeds the sum of their
--   costs by twice the cost of the unit direction times u.
--
--   Scope and conditions: Ordinary real analysis on supplied q: PairsAndNothingMore, two-homogeneity, nonnegativity and quarter-turn invariance imply q(x,y)=q(1,0)(x²+y²). Orthogonal additivity, arbitrary-rotation invariance and the stated normalized half-square follow. Parallelogram comparisons and controls expose the pair/quarter-turn roles. All four clauses remain explicit; no physical plane, realization of real coefficients, probability normalization or Born derivation is established.
--
--   Exact source statement:
--
--   ```lean
--   theorem cross_term_from_pairs_and_one_quarter_turn (q : ℝ → ℝ → ℝ)
--       (hpairs : PairsAndNothingMore q)
--       (hhom : ∀ t x y : ℝ, q (t * x) (t * y) = t * t * q x y)
--       (hnn : ∀ x y : ℝ, 0 ≤ q x y)
--       (hquarter : ∀ x y : ℝ, q (-y) x = q x y) (u v : ℝ) :
--       q (1 + u) (0 + v) - q 1 0 - q u v = 2 * q 1 0 * u
--   ```
-- source:
--   ['Theorems.Thm_APFPaper5_K1_plane_cost_from_pairs_and_one_quarter_turn:339; USB pullbacks v58 batch A; SHA-256 ab8e6269e3f57cb1aecd00e93f0a3cb5df150b1722b78a2e8ca4591058a2a8ec']

import Definitions.Def_APFPaper5_K1_PairsAndNothingMore
import Theorems.Thm_APFPaper5_K1_plane_cost_quadratic
import Theorems.Thm_APFPaper5_K1_square_of_cross_term
import Mathlib.Algebra.Order.Ring.Abs
set_option autoImplicit false

theorem APFPaper5.K1.cross_term_from_pairs_and_one_quarter_turn :
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
  (hquarter : ∀ (x y : Real), @Eq.{1} Real (q (@Neg.neg.{0} Real Real.instNeg y) x) (q x y)) (u v : Real),
  @Eq.{1} Real
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (q
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) u)
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) v))
        (q (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
      (q u v))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (q (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
      u) := by sorry
