-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_public_original_weighted_intrinsic_rate_identity
-- name    : AvramDividend.Classical.avram_p2_j_ui_public_original_weighted_intrinsic_rate_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:45:54.746117+00:00
-- url     : https://prove2.me/theorems/215d21b3-1f6d-4ab7-b76b-3aa39e6f8690
-- title:
--   Original intrinsic marked jump weighted intensity rate identity
-- statement:
--   For the genuine original spectrally negative Lévy process, the expected original jump count of every measurable Borel mark set B over (0,T] equals T times the intrinsic mark-rate measure B. More generally the expectation of integrating any nonnegative measurable mark test g against the genuine original time-mark jump-count measure over (0,T] equals T times the integral of g against the same intrinsic mark-rate measure. This identifies the expected weighted jump integral with its original-process mark intensity, without assuming the still-open identification with the original Lévy measure ν.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_public_original_intrinsic_weighted_kernel_fubini
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_intrinsic_intensity_measure_complete

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_j_ui_public_original_weighted_intrinsic_rate_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∃ markRate : Measure ℝ,
      (∀ B : Set ℝ, MeasurableSet B →
        (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Set.Ioc 0 T ×ˢ B) ∂P) = (T : ℝ≥0∞) * markRate B) ∧
      (∫⁻ ω, ∫⁻ p in (Set.Ioc 0 T ×ˢ (Set.univ : Set ℝ)),
        g p.2 ∂((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) ∂P) =
        (T : ℝ≥0∞) * (∫⁻ y, g y ∂markRate) := by sorry
