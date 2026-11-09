-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_nojump_zero_contact_weighted_cash_prefix
-- name    : AvramDividend.Classical.avram_bv_zero13_original_nojump_zero_contact_weighted_cash_prefix
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T22:56:35.766756+00:00
-- url     : https://prove2.me/theorems/32c4779c-117f-485d-a898-cca0841cb882
-- title:
--   Original arbitrary-admissible zero-contact weighted Stieltjes cash equals drift density on a surviving no-jump prefix
-- statement:
--   For the original finite-negative-jump-activity bounded-variation process and arbitrary adapted admissible dividends, on an actual surviving zero-reserve prefix without an original negative jump, the full Stieltjes dividend measure equals drift-scaled Lebesgue measure on the positive-time prefix. Consequently all nonnegative discounted cash weights agree. The right time-zero atom is excluded by Ioc and is zero under original active zero-reserve admissibility. The result handles a deterministic surviving prefix; first-jump endpoint and random restart time measurability remain separate.
-- source:
--   Source-exact combination of public Proved 28a916cf, original no-jump drift 2a0cae7c, and measure uniqueness 7ba7a474, with actual original-X, original-filtration, arbitrary adapted D and positive-prefix survival.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_active_zero_contact_Ioc_cash_eq_drift
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_no_jump_interval_is_drift_only
import Theorems.Thm_AvramDividend_Classical_measure_restrict_Ioc_eq_of_local_Ioc_agreement
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_zero13_original_nojump_zero_contact_weighted_cash_prefix
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (hDrift : 0 ≤ X.drift)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P,
      (T : ℝ≥0∞) < ruinTime X x D ω →
      (∀ u : ℝ≥0, u ≤ T → riskProcess X x D u ω = 0) →
      (∀ u : ℝ≥0, u ∈ Ioc (0 : ℝ≥0) T →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) →
      ∀ f : ℝ → ℝ≥0∞,
        (∫⁻ t in Ioc (0 : ℝ) (T : ℝ), f t
          ∂(dividendMeasure D ω)) =
        (∫⁻ t in Ioc (0 : ℝ) (T : ℝ), f t
          ∂((ENNReal.ofReal X.drift) • volume)) := by sorry
