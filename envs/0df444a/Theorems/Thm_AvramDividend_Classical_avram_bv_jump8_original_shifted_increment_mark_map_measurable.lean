-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_original_shifted_increment_mark_map_measurable
-- name    : AvramDividend.Classical.avram_bv_jump8_original_shifted_increment_mark_map_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:33:02.536641+00:00
-- url     : https://prove2.me/theorems/e2ab3e9a-b90e-4a2d-9d09-231ea66496ad
-- title:
--   Actual source shifted-increment path has Borel measurable intrinsic time-jump-mark map
-- statement:
--   For each fixed original Lévy sample and integer shift, the actual stationary future-increment path's exact jump mark is Borel in relative time, using pathwise càdlàg and original jointly Borel evaluation. No independent replacement process or Poisson measure assumption.
-- source:
--   Apply Proved original joint evaluation, Proved shifted future càdlàg 984180e2 and Proved generic joint left-limit measurability 2a1def10 on sample space Unit. Supports samepath shift rectangle target 5714bfe7.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_original_shifted_increment_mark_map_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (n : ℕ) :
    Measurable (fun u : ℝ≥0 =>
      (u, (X.X ((n : ℝ≥0) + u) ω - X.X (n : ℝ≥0) ω) -
        Function.leftLim
          (fun v : ℝ≥0 => X.X ((n : ℝ≥0) + v) ω -
            X.X (n : ℝ≥0) ω) u)) := by sorry
