-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_all_caps_source_ubv_value_from_ae_future_clock_budget
-- name    : AvramDividend.Classical.avram_wave7_11_all_caps_source_ubv_value_from_ae_future_clock_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:37:58.278485+00:00
-- url     : https://prove2.me/theorems/60b0f666-d7a1-4ae6-b5e6-7cdd58131f3e
-- title:
--   All-cap original UBV finite-horizon value from one almost surely later source clock budget
-- statement:
--   For the canonical original spectrally negative Lévy law P, filter 𝓕 and its true HJB generator and Stieltjes dividend payout, the finite-horizon UBV verification bound holds at all dividend caps including zero, provided that at positive cap and strictly positive initial reserve there is one sample-dependent auxiliary localising clock strictly after T almost surely, with the expected source stopped cash budget. At cap zero no stochastic estimate is needed: the corrected zero-cap source Stieltjes theorem applies. This retains w(0)≥0 and the original time-zero and horizon payment atoms.
-- source:
--   Proved source local HJB side conditions d307095e, Proved corrected zero-cap theorem, and newly Proved positive-cap a.e.-future conditional value bridge (after publication).

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_local_verification_stochastic_core_side_conditions
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_zero_cap_original_stieltjes_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_source_ubv_value_from_ae_future_clock_budget
import Mathlib.Data.Real.Basic

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_all_caps_source_ubv_value_from_ae_future_clock_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T)
    (hAeClock : 0 < C → 0 < x →
      ∃ η : Ω → ℝ≥0∞,
        (∀ᵐ ω ∂P, ENNReal.ofReal T < η ω) ∧
        (∫⁻ ω, ∫⁻ t in paymentTimes
          (min (ruinTime X x D ω) (η ω)) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
          ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
