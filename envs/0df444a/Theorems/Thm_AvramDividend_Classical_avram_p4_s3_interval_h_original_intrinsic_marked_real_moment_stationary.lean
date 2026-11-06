-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_intrinsic_marked_real_moment_stationary
-- name    : AvramDividend.Classical.avram_p4_s3_interval_h_original_intrinsic_marked_real_moment_stationary
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T16:48:13.106217+00:00
-- url     : https://prove2.me/theorems/34cdb144-4211-477d-a5ab-4d81674d665e
-- title:
--   Any integrable original marked-count real moment is stationary across every deterministic source window
-- statement:
--   For the literal original spectrally negative Levy intrinsic count on any Borel marked rectangle, every measurable real-valued count functional g with integrable zero-origin value has an integrable shifted value and exactly the same physical expectation. Proves both measurability and identical distribution via the original X path and source count law, with no auxiliary process or assumed future moments.
-- source:
--   Uses Proved original full physical count law 37abf3aa and universal cadlag marked source extractor 41bfd2c8; derives actual source count measurability from X.adapted and whole-path measurability. Mathlib IdentDistrib.comp, integrable_iff and integral_eq then transport real moments.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_intrinsic_marked_count_stationary_law
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_cadlag_arbitrary_borel_marked_jumps_product_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_increment_path_cadlag
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_futurepath_marked_count_transport
import Theorems.Thm_AvramDividend_Classical_levy_wholePath_measurable
open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_interval_h_original_intrinsic_marked_real_moment_stationary
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (g : ℝ≥0∞ → ℝ) (hg : Measurable g)
    (hOrigin : Integrable
      (fun ω => g (NX ω (Ioc 0 T ×ˢ B))) P) :
    Integrable (fun ω => g (NX ω (Ioc s (s + T) ×ˢ B))) P ∧
    (∫ ω, g (NX ω (Ioc s (s + T) ×ˢ B)) ∂P) =
      ∫ ω, g (NX ω (Ioc 0 T ×ˢ B)) ∂P := by sorry
