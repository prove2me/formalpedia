-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_postpayment_candidate_strict_positive_atomless_preruin
-- name    : AvramDividend.Classical.avram_wave5_ubv_original_postpayment_candidate_strict_positive_atomless_preruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:40:17.145831+00:00
-- url     : https://prove2.me/theorems/35725277-b39c-4a8d-8b04-828ff9b7d8a0
-- title:
--   Original post-payment verification value strictly positive at all atomless typical pre-ruin times and caps
-- statement:
--   For the actual spectrally negative Lévy process X on its source filtration 𝓕, actual admissible dividend strategy D and any cap, with UBV and the corrected core's w0, continuity and interior C2 gradient hypotheses, w of the reserve immediately after right dividend payments, w(x+X.X t−rightLimit D t), is strictly positive at μ-a.e positive time strictly before any pre-ruin localiser σ≤ruinTime, for P-a.e path. The μ assumptions are only SFinite and NullSingletonClass, inherited from the already Proved original zero-occupation/predictable sign and atomless continuity theorems. This does not assert strict positivity at a dividend atom or at ruin; there, separate nonnegative terminal theorems apply. No Stieltjes or Ito-Meyer integration is duplicated.
-- source:
--   Corrected UBV core 429e17ca-5528-40b5-b593-7c03973d0706, Proved original predictable candidate strict positivity 01d0d28c-106a-4e9d-bef5-7418e4279899, and original postpayment reserve atomless continuity 2c5e035b-c9bf-4b4b-b635-3029428f3945. No milestone changes.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_predictable_candidate_strict_positive_before_localiser
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_postpayment_reserve_atomless_continuity

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_ubv_original_postpayment_candidate_strict_positive_atomless_preruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (σ : Ω → ℝ≥0∞) (hσ : ∀ ω, σ ω ≤ ruinTime X x D ω)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ] :
    ∀ᵐ ω ∂P, ∀ᵐ (t : ℝ≥0) ∂μ,
      (0 < t ∧ (t : ℝ≥0∞) < σ ω) →
        0 < w (x + X.X t ω - rightLimit D t ω) := by sorry
