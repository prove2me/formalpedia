-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_public_original_intrinsic_mark_marginal
-- name    : AvramDividend.Classical.avram_p2_j_ui_public_original_intrinsic_mark_marginal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:40:49.375494+00:00
-- url     : https://prove2.me/theorems/b74a5170-a83f-484d-81f5-2ac2ea76f0a3
-- title:
--   Original intrinsic time-mark mean measure has its genuine jump intensity as unit-time mark marginal
-- statement:
--   For the actual original spectrally negative Lévy process, there are an expected time-mark jump measure Q and the intrinsically constructed rate measure markRate. Q is the expected original intrinsic count on every measurable time-mark set. Its unit-time mark marginal is exactly markRate, and each original time-mark rectangle has Q mass T multiplied by markRate(B). This identifies the two independently constructed measures without presuming equality with the original Lévy measure.

import Mathlib.MeasureTheory.Measure.GiryMonad
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_event_weighted_marked_count_is_measure
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_intrinsic_intensity_measure_complete

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_j_ui_public_original_intrinsic_mark_marginal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ Q : Measure (ℝ≥0 × ℝ), ∃ markRate : Measure ℝ,
      (∀ C : Set (ℝ≥0 × ℝ), MeasurableSet C →
        Q C = (∫⁻ ω,
          ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            C ∂P)) ∧
      ((Q.restrict (Set.Ioc 0 (1 : ℝ≥0) ×ˢ Set.univ)).map Prod.snd) = markRate ∧
      (∀ (T : ℝ≥0) (B : Set ℝ), MeasurableSet B →
        Q (Set.Ioc 0 T ×ˢ B) = (T : ℝ≥0∞) * markRate B) := by sorry
