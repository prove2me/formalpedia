-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_prejump_candidate_nonnegative_atomless_allcap
-- name    : AvramDividend.Classical.avram_wave5_ubv_original_prejump_candidate_nonnegative_atomless_allcap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:19:12.352779+00:00
-- url     : https://prove2.me/theorems/656eae19-5690-483c-a5b2-25996d16c07f
-- title:
--   Actual original predictable left-limit candidate is nonnegative at every atomless observation time and all caps
-- statement:
--   For any actual SpectrallyNegativeLevy P 𝓕, admissible dividend strategy D and cap C (including C=0 or C=∞), under exactly the corrected core's 0≤w0, continuousOn nonnegative, zero-on-negative, interior C2 and gradient assumptions, the candidate w evaluated at the predictable left limit of the original post-payment reserve is nonnegative for P-a.e path and μ-a.e strictly positive observation time. The measure μ need only have null singletons; no sigma finiteness, bounded variation, positive cap, no-creeping, or boundary C2 assumptions. The proof transfers a Proved original atomless pre-jump/book-reserve equality into a Proved all-cap nonnegative book-reserve theorem. This is an endpoint sign lemma, not controlled Ito-Meyer or dividend Stieltjes integration.
-- source:
--   Corrected UBV core 429e17ca-5528-40b5-b593-7c03973d0706; Proved original atomless pre-jump equality 89e50cbf-efd7-4c66-8cd6-2d1e99de1a8d and original allcap terminal nonnegative c7bf9b3b-8066-4109-a2fc-b9ac81e3ca0f. Does not submit to or modify core or milestones.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_original_prejump_equals_book_reserve_atomless_nnreal_clock
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_all_cap_stopped_terminal_candidate_nonnegative

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_ubv_original_prejump_candidate_nonnegative_atomless_allcap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (μ : Measure ℝ≥0) [NullSingletonClass μ] :
    ∀ᵐ ω ∂P, ∀ᵐ t ∂μ, 0 < t →
      0 ≤ w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) := by sorry
