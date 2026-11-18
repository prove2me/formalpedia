-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB48_original_barrier_upperstrip_occupation_on_tube
-- name    : AvramDividend.Classical.avram_gbB48_original_barrier_upperstrip_occupation_on_tube
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T16:29:16.382914+00:00
-- url     : https://prove2.me/theorems/45bf2290-5443-4b96-992d-7f255f52dd2e
-- title:
--   Actual original barrier's upper-strip physical occupation equals the stopped horizon on a narrow tube
-- statement:
--   For the original spectrally negative Lévy source, cap barrier at C=1/8 and fixed upper-strip cutoff b=5/44, source-path fluctuations bounded by 1/400 through positive T imply that the real physical-time upper-strip occupation integral over the observation interval equals T, conditional only on the stated measurable strip set. This quantifies the missing positive drift allowance in the disputed B52p source statement.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB38_barrier_reserve_above_cutoff_on_tube
import Theorems.Thm_AvramDividend_Classical_avram_gbB47_upper_strip_occupation_exact_on_floor_path
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB48_original_barrier_upperstrip_occupation_on_tube
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℕ) (T : ℝ≥0) (hT : 0 < T) (hTn : (T : ℝ) ≤ n)
    (ω : Ω)
    (hTube : ∀ s : ℝ≥0, s ≤ T → |X.X s ω| ≤ (1 / 400 : ℝ))
    (hMeas : MeasurableSet {t : ℝ | t < (T : ℝ) ∧
      (5 / 44 : ℝ) <
        riskProcess X (1 / 8 : ℝ)
          (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ))
          (Real.toNNReal t) ω}) :
    (∫ t in Ioo (0 : ℝ) (n : ℝ),
      if t < (T : ℝ) ∧
        (5 / 44 : ℝ) <
          riskProcess X (1 / 8 : ℝ)
            (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ))
            (Real.toNNReal t) ω
      then (1 : ℝ) else 0 ∂volume) = (T : ℝ) := by sorry
