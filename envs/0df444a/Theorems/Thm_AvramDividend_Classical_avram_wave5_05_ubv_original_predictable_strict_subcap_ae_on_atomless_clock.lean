-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_strict_subcap_ae_on_atomless_clock
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_strict_subcap_ae_on_atomless_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:30:39.24809+00:00
-- url     : https://prove2.me/theorems/0687dddb-de6f-4231-9a0b-865fb66a9bd2
-- title:
--   True original UBV predictable pre-event reserve lies strictly below cap at almost every surviving atomless physical-clock time
-- statement:
--   For genuine spectrally negative unbounded-variation Lévy source X, same-filtration actual dividend strategy D with capped original reserve U, and any fixed s-finite atomless time clock μ, there is a P-full original-process event on which μ-almost every positive pre-ruin time has strict inequality leftLim(x+X−rightLimit D)_t<c. The leftLim expression is the actual chronological predictable pre-event reserve used in source jump and Gaussian drift characteristics, rather than the book current value. This holds even if U0=c or arbitrary later cap contacts occur, and needs no endpoint derivative or strict-below-cap dividend-payment assumption. It does not imply singular local-time or dividend Stieltjes nullity.
-- source:
--   Proved original same-source UBV occupation cc500549-ba08-47b0-b5c0-07c7a9bb40f3 and leftLim/current chronology bridge 89e50cbf-efd7-4c66-8cd6-2d1e99de1a8d. Supports corrected core 429e17ca-5528-40b5-b593-7c03973d0706 unchanged.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_same_source_sigma_finite_cap_occupation
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_original_prejump_equals_book_reserve_atomless_nnreal_clock

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_strict_subcap_ae_on_atomless_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω → riskProcess X x D s ω ≤ c)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ] :
    ∀ᵐ ω ∂P, ∀ᵐ t : ℝ≥0 ∂μ,
      0 < t → (t : ℝ≥0∞) < ruinTime X x D ω →
        Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t < c := by sorry
