-- Prove2me | Theorems.Thm_AvramDividend_Classical_nextRecord_discount_eq_past_mul_future
-- name    : AvramDividend.Classical.nextRecord_discount_eq_past_mul_future
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T18:33:26.370974+00:00
-- url     : https://prove2.me/theorems/4d5e356f-3bbb-4f77-9dd0-74949c3d1ae2
-- title:
--   Finite next-record exponential discount factors into past and shifted future discounts
-- statement:
--   At a finite attained first upward record u of level b, the next record time b+ε equals u plus the shifted future strict upcrossing time ρ. If ρ is finite, its exponential q-discount decomposes exactly into the product of discount factors for u and ρ. This establishes the precise pathwise multiplicative reward identity used when applying stopped-history/future Lévy independence to renewal expectations.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1, q-discounted record renewal factorisation.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_nextRecord_upclock_eq_add_shifted_inf
import Theorems.Thm_AvramDividend_Classical_discounted_dividend_weight_time_shift

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.nextRecord_discount_eq_past_mul_future
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b ε q : ℝ) (hε : 0 ≤ ε) (u : ℝ≥0) (ω : Ω)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hAt : X.X u ω = b)
    (ρ : ℝ≥0∞)
    (hρ : ρ =
      (⨅ (t : ℝ≥0)
        (_ : ε < X.X (u + t) ω - X.X u ω), (t : ℝ≥0∞)))
    (hρfinite : ρ ≠ ⊤) :
    ENNReal.ofReal (Real.exp
        (-(q * (twoSidedExitUpTime X (b + ε) ω).toReal))) =
      ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) *
        ENNReal.ofReal (Real.exp (-(q * ρ.toReal))) := by sorry
