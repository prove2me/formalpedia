-- Prove2me | Theorems.Thm_APFPaper5_K1_at_the_eighth_turn_the_pair_number_squared_is_a_half
-- name    : APFPaper5.K1.at_the_eighth_turn_the_pair_number_squared_is_a_half
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-22T03:58:30.395994+00:00
-- url     : https://prove2.me/theorems/c69971e2-d9aa-41a3-a21d-38b2bf15d13c
-- title:
--   at the eighth turn the pair number squared is a half
-- statement:
--   Under the four clauses, for the direction an eighth of a turn from the unit direction, the pair
--   number squared is a half. The direction is (u, u) with u * u + u * u = 1; no square root is used.
--
--   Scope and conditions: Ordinary real analysis on supplied q: PairsAndNothingMore, two-homogeneity, nonnegativity and quarter-turn invariance imply q(x,y)=q(1,0)(x²+y²). Orthogonal additivity, arbitrary-rotation invariance and the stated normalized half-square follow. Parallelogram comparisons and controls expose the pair/quarter-turn roles. All four clauses remain explicit; no physical plane, realization of real coefficients, probability normalization or Born derivation is established.
--
--   Exact source statement:
--
--   ```lean
--   theorem at_the_eighth_turn_the_pair_number_squared_is_a_half (q : ℝ → ℝ → ℝ)
--       (hpairs : PairsAndNothingMore q)
--       (hhom : ∀ t x y : ℝ, q (t * x) (t * y) = t * t * q x y)
--       (hnn : ∀ x y : ℝ, 0 ≤ q x y)
--       (hquarter : ∀ x y : ℝ, q (-y) x = q x y) (hc : q 1 0 ≠ 0) (u : ℝ)
--       (hu : u * u + u * u = 1) :
--       (q (1 + u) (0 + u) - q 1 0 - q u u) / (2 * q 1 0) *
--         ((q (1 + u) (0 + u) - q 1 0 - q u u) / (2 * q 1 0)) = 1 / 2
--   ```
-- source:
--   ['Theorems.Thm_APFPaper5_K1_plane_cost_from_pairs_and_one_quarter_turn:350; USB pullbacks v58 batch A; SHA-256 ab8e6269e3f57cb1aecd00e93f0a3cb5df150b1722b78a2e8ca4591058a2a8ec']

import Definitions.Def_APFPaper5_K1_PairsAndNothingMore
import Theorems.Thm_APFPaper5_K1_plane_cost_quadratic
import Theorems.Thm_APFPaper5_K1_square_of_cross_term
import Mathlib.Algebra.Order.Ring.Abs
set_option autoImplicit false

theorem APFPaper5.K1.at_the_eighth_turn_the_pair_number_squared_is_a_half :
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
  (hquarter : ∀ (x y : Real), @Eq.{1} Real (q (@Neg.neg.{0} Real Real.instNeg y) x) (q x y))
  (hc :
    @Ne.{1} Real
      (q (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
  (u : Real)
  (hu :
    @Eq.{1} Real
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) u u)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) u u))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))),
  @Eq.{1} Real
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (q
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) u)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) u))
            (q (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
          (q u u))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
          (q (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (q
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) u)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) u))
            (q (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
          (q u u))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
          (q (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
      (@OfNat.ofNat.{0} Real (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))) := by sorry
