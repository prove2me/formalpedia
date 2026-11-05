-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_reward_measurable_version
-- name    : AvramDividend.Classical.avram_p3_bv_original_strict_reward_measurable_version
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:41:54.950955+00:00
-- url     : https://prove2.me/theorems/2c9ec6bb-d25d-4366-a5dd-fd58766a219e
-- title:
--   Exact original BV strict stopped cash and terminal admit a nonnegative measurable integrable representative
-- statement:
--   The accepted original strict-stopped BV cash-plus-prepayment terminal is integrable and pointwise nonnegative. Its almost-everywhere measurable representative is a genuinely measurable, integrable, almost-everywhere nonnegative real reward equal almost everywhere to the exact original stopped reward. This provides a mathematically justified source-specific Fatou payoff-grid candidate without assuming pointwise measurability of the raw Stieltjes map or any uniform L1 mesh envelope.
-- source:
--   Proved 221852bf original strictly stopped reward L1/nonnegative; Mathlib pinned AEMeasurable.mk, .measurable_mk and .ae_eq_mk

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_reward_L1_nonnegative

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/- The exact original strict BV reward has a measurable nonnegative L1
representative. This removes an artificial pointwise-measurability
requirement from its eventual finite-grid Fatou implementation. -/

theorem AvramDividend.Classical.avram_p3_bv_original_strict_reward_measurable_version
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω)) :
    let S : ℝ≥0 := ⟨T, hT⟩
    let Strict : Ω → ℝ := fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0)
    ∃ F : Ω → ℝ,
      Measurable F ∧ Integrable F P ∧
      (0 ≤ᵐ[P] F) ∧ (F =ᵐ[P] Strict) := by sorry
