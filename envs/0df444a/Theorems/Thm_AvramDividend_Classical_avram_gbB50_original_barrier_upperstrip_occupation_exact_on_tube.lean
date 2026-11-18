-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB50_original_barrier_upperstrip_occupation_exact_on_tube
-- name    : AvramDividend.Classical.avram_gbB50_original_barrier_upperstrip_occupation_exact_on_tube
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T16:33:23.348007+00:00
-- url     : https://prove2.me/theorems/a211dafc-13b0-4123-a0f9-60d603d8742f
-- title:
--   Original cap barrier upper-strip occupation equals the stopped horizon without measurability assumptions
-- statement:
--   For the true original spectrally negative Lévy source and original cap barrier at x=C=1/8, any positive bounded horizon T with a narrow source tube has strictly pre-horizon upper-strip occupation exactly T, with no separate measurability assumption. This quantifies the omitted finite-j positive drift contribution in the original Gaussian source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB48_original_barrier_upperstrip_occupation_on_tube
import Theorems.Thm_AvramDividend_Classical_avram_gbB49_original_barrier_upperstrip_section_measurable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB50_original_barrier_upperstrip_occupation_exact_on_tube
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℕ) (T : ℝ≥0) (hT : 0 < T) (hTn : (T : ℝ) ≤ n)
    (ω : Ω)
    (hTube : ∀ s : ℝ≥0, s ≤ T → |X.X s ω| ≤ (1 / 400 : ℝ)) :
    (∫ t in Ioo (0 : ℝ) (n : ℝ),
      if t < (T : ℝ) ∧
        (5 / 44 : ℝ) <
          riskProcess X (1 / 8 : ℝ)
            (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ))
            (Real.toNNReal t) ω
      then (1 : ℝ) else 0 ∂volume) = (T : ℝ) := by sorry
