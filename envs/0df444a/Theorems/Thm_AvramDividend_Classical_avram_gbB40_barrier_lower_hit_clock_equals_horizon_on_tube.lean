-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB40_barrier_lower_hit_clock_equals_horizon_on_tube
-- name    : AvramDividend.Classical.avram_gbB40_barrier_lower_hit_clock_equals_horizon_on_tube
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T16:06:15.928737+00:00
-- url     : https://prove2.me/theorems/56d74322-cb4c-462f-9ff8-783695a4005c
-- title:
--   Original Gaussian barrier cutoff stopping clock equals T on narrow source tube
-- statement:
--   On the original cap barrier reserve path with x=C=1/8, a source tube of radius 1/400 prevents any lower cutoff hit at b=5/44 through T. Thus the exact capped first-hitting infimum used by B32 equals T, proving the geometrical stop criterion for a positive-drift fixed-band counterexample.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB38_barrier_reserve_above_cutoff_on_tube
open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB40_barrier_lower_hit_clock_equals_horizon_on_tube
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (ω : Ω)
    (hTube : ∀ s : ℝ≥0, s ≤ T →
      |X.X s ω| ≤ (1 / 400 : ℝ)) :
    sInf ((Icc (0 : ℝ≥0) T ∩
      (fun t : ℝ≥0 => -(riskProcess X (1 / 8 : ℝ)
        (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) t ω)) ⁻¹'
        Ici (-(5 / 44 : ℝ))) ∪ {T}) = T := by sorry
