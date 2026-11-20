-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_ruin_clipped_natural_clock_real_measurable
-- name    : AvramDividend.Classical.avram_jump6_B_original_ruin_clipped_natural_clock_real_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T12:26:09.726627+00:00
-- url     : https://prove2.me/theorems/b9048ba3-43af-43dc-9c07-e662724e6eeb
-- title:
--   Original spectrally negative Levy natural ruin-clipped horizon real clock is measurable
-- statement:
--   For any original spectrally negative Levy process, admissible dividend strategy, starting reserve, cap and finite natural horizon, the real-valued natural clock min(ruinTime,n).toNNReal is measurable. Invoke the already Proved double-min stopping-time real-clock measurability theorem with the second localisation clock chosen as deterministic n, for which the extra min is idempotent.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_double_min_clock_real_measurable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_original_ruin_clipped_natural_clock_real_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) :
    Measurable (fun ω : Ω =>
      (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ)) := by sorry
