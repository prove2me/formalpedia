-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB38_barrier_reserve_above_cutoff_on_tube
-- name    : AvramDividend.Classical.avram_gbB38_barrier_reserve_above_cutoff_on_tube
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T15:51:55.413172+00:00
-- url     : https://prove2.me/theorems/24b81fed-fdc4-452a-b3b7-9c1a1c11f743
-- title:
--   Original reflected Gaussian barrier reserve remains above cutoff on narrow tube
-- statement:
--   For the original cap barrier at x=C=1/8, if the source path remains within 1/400 on the entire prefix [0,t], the running-supremum barrier dividend regulator is at most 1/400 and the prepayment risk reserve stays strictly above fixed cutoff b=5/44. This proves the deterministic cap-reflection geometry required by the positive Gaussian counterexample.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB38_barrier_reserve_above_cutoff_on_tube
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (ω : Ω)
    (hTube : ∀ s : ℝ≥0, s ≤ t →
      |X.X s ω| ≤ (1 / 400 : ℝ)) :
    (5 / 44 : ℝ) <
      riskProcess X (1 / 8 : ℝ)
        (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) t ω := by sorry
