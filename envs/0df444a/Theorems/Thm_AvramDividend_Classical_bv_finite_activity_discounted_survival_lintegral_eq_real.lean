-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_finite_activity_discounted_survival_lintegral_eq_real
-- name    : AvramDividend.Classical.bv_finite_activity_discounted_survival_lintegral_eq_real
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:33:21.05565+00:00
-- url     : https://prove2.me/theorems/cb35114c-9f12-4c9c-ae54-97938e912033
-- title:
--   Discounted finite-activity survival Tonelli kernel equals the exact real exponential drift integral
-- statement:
--   Under finite jump intensity, positive discount and the bounded-variation standing assumptions, the strict-survival discounted drift kernel evaluates to the nonnegative embedding of its ordinary real-valued exponential integral. This reconciles the exact ruin-clock Tonelli formula with the classical first-jump dividend payout and controls integrability through the positive combined discount and jump rate.
-- source:
--   Avram, Palmowski and Pistorius (2007); exact finite-activity first-jump survival law, pinned Mathlib exponential-integrability and nonnegative integral-conversion theorems.

import Theorems.Thm_AvramDividend_Classical_bv_reflected_strict_survival_measure_exp_first_jump
import Theorems.Thm_AvramDividend_Classical_first_jump_discount_survival_kernel_product
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Restrict

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_finite_activity_discounted_survival_lintegral_eq_real
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hStanding : X.Standing)
    (q : ℝ) (hq : 0 < q) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    (∫⁻ t in Ioi (0 : ℝ),
      P {ω : Ω | ENNReal.ofReal t < barrierRuinTime X 0 ω} *
        ENNReal.ofReal (X.drift * Real.exp (-(q * t))) ∂volume) =
    ENNReal.ofReal (∫ t : ℝ in Ioi (0 : ℝ),
      X.drift * Real.exp
        (-(q + (X.ν (Iio (0 : ℝ))).toReal) * t) ∂volume) := by sorry
