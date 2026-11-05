-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_bounded_random_clock_closed_cash_atom_split_and_reward_L1
-- name    : AvramDividend.Classical.avram_p3_g2_original_bounded_random_clock_closed_cash_atom_split_and_reward_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T23:16:14.5369+00:00
-- url     : https://prove2.me/theorems/e1a2cbb1-4cb8-4410-9f3b-c4125006feb8
-- title:
--   Original bounded random-clock exact strict/closed Stieltjes atom partition and integrable signed postpayment reward
-- statement:
--   For any measurable finite bounded physical observation clock, complete original ruin-stopped Stieltjes payout equals strict-before-clock cash plus exactly one active right endpoint dividend atom, including the zero clock; the sum of closed cash and the actual signed strict-survival post-rightLimit terminal is integrable. This is for source X, actual D, positive cap and contact without equality-in-law or stopping-time assumption.
-- source:
--   Proved source 54ad337e pointwise all-clock closed/strict/active atom identity; 3deca135 original bounded random-clock complete cash L1; 10c9f283 G2 source-exact signed postpayment random-clock terminal L1 (public).

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_closed_cash_eq_strict_plus_active_right_atom
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_bounded_random_clock_full_stieltjes_cash_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_bounded_random_clock_signed_postterminal_L1

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g2_original_bounded_random_clock_closed_cash_atom_split_and_reward_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτMeas : Measurable τ) (hτBound : ∀ ω, τ ω ≤ H) :
    (∀ ω : Ω,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (τ ω : ℝ))) *
          (rightLimit D (τ ω) ω - D (τ ω) ω)
      else 0)) ∧
    Integrable (fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (τ ω : ℝ))) *
          w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω)
      else 0)) P := by sorry
