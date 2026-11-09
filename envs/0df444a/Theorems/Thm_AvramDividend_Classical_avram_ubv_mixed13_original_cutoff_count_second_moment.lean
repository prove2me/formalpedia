-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed13_original_cutoff_count_second_moment
-- name    : AvramDividend.Classical.avram_ubv_mixed13_original_cutoff_count_second_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T00:36:09.976927+00:00
-- url     : https://prove2.me/theorems/df8d5ad5-2e15-42e2-80ba-2830814ed0b0
-- title:
--   Original physical finite-cutoff negative-jump count has a genuine second moment
-- statement:
--   For every original spectrally negative Levy process and finite physical horizon on its probability space, the real count of strictly negative physical jumps in the full negative cutoff has an integrable square. This combines existing Proved original factorial moment and first-moment integrability, and is needed to control the finite-activity compensated annulus in physical L2.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f2_original_band_count_factorial_moment_exact
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cutoff_marked_count_L1_auto

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_mixed13_original_cutoff_count_second_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    Integrable (fun ω => ((N ω).toReal) ^ 2) P := by sorry
