-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_admissible_finitecap_predictable_hjb_ae
-- name    : AvramDividend.Classical.avram_wave7_18_original_admissible_finitecap_predictable_hjb_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:50:43.701389+00:00
-- url     : https://prove2.me/theorems/a8b46313-adfa-4b01-96a3-3ec17cfd7554
-- title:
--   Original UBV finite-cap predictable C² HJB support from canonical admissibility and initial reserve
-- statement:
--   On the genuine original spectrally negative UBV Lévy process and source IsAdmissibleLe dividend control, assume only nonnegative initial reserve x with ENNReal.ofReal x≤ENNReal.ofReal c for a positive finite real cap c, plus exact ContDiffOn ℝ 2 w and source HJB/generator/gradient hypotheses. The already Proved canonical cap-range-before-ruin lemma converts admissible current cap into a pathwise real cap using ENNReal.ofReal_le_ofReal_iff. The now Proved W7-18 source occupation theorem then places the true predictable left-limit postpayment reserve strictly inside the cap P×μ-a.e. before any ruin-dominated clock, with all C², generator and gradient conclusions. This final interface does not add an assumed a.e. cap support nor an explicit extra real cap assumption, and makes no Ito claim.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_riskProcess_range_before_ruin_including_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_finite_realcap_predictable_hjb_from_source_occupation

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_18_original_admissible_finitecap_predictable_hjb_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q c : ℝ) (hc : 0 < c) (w : ℝ → ℝ)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < ENNReal.ofReal c →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < ENNReal.ofReal c →
      1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (σ : Ω → ℝ≥0∞) (hσ : ∀ ω, σ ω ≤ ruinTime X x D ω)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ] :
    ∀ᵐ ω ∂P, ∀ᵐ (t : ℝ≥0) ∂μ,
      (0 < t ∧ (t : ℝ≥0∞) < σ ω) →
      let y : ℝ := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
      (0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c) ∧
        ContDiffWithinAt ℝ 2 w
          {z : ℝ | 0 < z ∧ ENNReal.ofReal z < ENNReal.ofReal c} y ∧
        X.GeneratorIntegrable w y ∧
        X.generator w y - q * w y ≤ 0 ∧ 1 ≤ deriv w y := by sorry
