-- Prove2me | Theorems.Thm_APFPaper5_K1_pairs_and_reversal_unseen_give_the_parallelogram
-- name    : APFPaper5.K1.pairs_and_reversal_unseen_give_the_parallelogram
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-22T06:51:11.842884+00:00
-- url     : https://prove2.me/theorems/5ccb37d3-61cb-4899-ae4f-65b7fcdd110e
-- title:
--   pairs and reversal unseen give the parallelogram
-- statement:
--   On the plane, the named clause gives the parallelogram clause when the cost of a reversed combination
--   is the same.
--
--   Scope and conditions: Ordinary real analysis on supplied q: PairsAndNothingMore, two-homogeneity, nonnegativity and quarter-turn invariance imply q(x,y)=q(1,0)(x²+y²). Orthogonal additivity, arbitrary-rotation invariance and the stated normalized half-square follow. Parallelogram comparisons and controls expose the pair/quarter-turn roles. All four clauses remain explicit; no physical plane, realization of real coefficients, probability normalization or Born derivation is established.
--
--   Exact source statement:
--
--   ```lean
--   theorem pairs_and_reversal_unseen_give_the_parallelogram (q : ℝ → ℝ → ℝ)
--       (hpairs : PairsAndNothingMore q) (hrev : ∀ x y : ℝ, q (-x) (-y) = q x y) :
--       ∀ x1 y1 x2 y2 : ℝ,
--         q (x1 + x2) (y1 + y2) + q (x1 - x2) (y1 - y2) = 2 * q x1 y1 + 2 * q x2 y2
--   ```
-- source:
--   ['Theorems.Thm_APFPaper5_K1_plane_cost_from_pairs_and_one_quarter_turn:384; USB pullbacks v58 batch A; SHA-256 ab8e6269e3f57cb1aecd00e93f0a3cb5df150b1722b78a2e8ca4591058a2a8ec']

import Definitions.Def_APFPaper5_K1_PairsAndNothingMore
import Theorems.Thm_APFPaper5_K1_plane_cost_quadratic
import Theorems.Thm_APFPaper5_K1_square_of_cross_term
import Mathlib.Algebra.Order.Ring.Abs
set_option autoImplicit false

theorem APFPaper5.K1.pairs_and_reversal_unseen_give_the_parallelogram :
∀ (q : Real → Real → Real) (hpairs : APFPaper5.K1.PairsAndNothingMore q)
  (hrev :
    ∀ (x y : Real), @Eq.{1} Real (q (@Neg.neg.{0} Real Real.instNeg x) (@Neg.neg.{0} Real Real.instNeg y)) (q x y))
  (x1 y1 x2 y2 : Real),
  @Eq.{1} Real
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (q (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) x1 x2)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) y1 y2))
      (q (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) x1 x2)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) y1 y2)))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (q x1 y1))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (q x2 y2))) := by sorry
