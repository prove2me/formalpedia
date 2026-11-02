-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_predictable_preruin_strict_interior_atomless
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_preruin_strict_interior_atomless
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:27:14.002588+00:00
-- url     : https://prove2.me/theorems/c9db7a94-e185-4483-b0d9-b79a2d3a7487
-- title:
--   Original same-source UBV predictable reserve is strictly in the generator interior for every positive finite or infinite cap at atomless-clock a.e. pre-ruin time
-- statement:
--   Under the corrected UBV source and the exact original jointly adapted capped dividend strategy, the true chronological predictable strict-left pre-event surplus (not just riskProcess at the current timestamp) lies strictly between zero and any nonzero extended cap C at almost every positive pre-ruin time, for any predetermined atomless s-finite NNReal clock. This applies to finite C>0, initial x=C, and C=∞. It combines original X,D cap/zero occupation with the accepted NNReal-time predictable/current chronology bridge, without replacing the process by an equal-law copy or assuming payments avoid cap contact. It gives direct support for HJB and source generator coefficients evaluated at the correct Itô pre-jump state.
-- source:
--   Proved original-X,D UBV no-grid strict generator-domain occupation bd222a39-c2dd-4836-ab7e-20c75561dcda; accepted actual pre-event/current NNReal atomless bridge 89e50cbf-efd7-4c66-8cd6-2d1e99de1a8d; corrected canonical core 429e17ca-5528-40b5-b593-7c03973d0706. No milestone or core changes.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_allcap_actual_generator_interior_no_grid
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_original_prejump_equals_book_reserve_atomless_nnreal_clock

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave5_05_ubv_original_predictable_preruin_strict_interior_atomless
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hC0 : C ≠ 0)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (μ : Measure ℝ≥0) [SFinite μ] [NullSingletonClass μ] :
    ∀ᵐ ω ∂P, ∀ᵐ (t : ℝ≥0) ∂μ,
      (0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω) →
        0 < Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ∧
        ENNReal.ofReal (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) < C := by sorry
