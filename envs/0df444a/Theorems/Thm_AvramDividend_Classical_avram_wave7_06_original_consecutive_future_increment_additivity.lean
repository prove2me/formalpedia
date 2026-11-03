-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_consecutive_future_increment_additivity
-- name    : AvramDividend.Classical.avram_wave7_06_original_consecutive_future_increment_additivity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T15:49:34.319765+00:00
-- url     : https://prove2.me/theorems/3ddf6f45-bb40-4d1f-9ed5-42f953f57a38
-- title:
--   Original future increment telescopes across adjacent original filtration cells
-- statement:
--   For every original ω and consecutive nonnegative time steps u,v after s, the terminal source increment over u+v is exactly the sum of its two successive source increments. This pathwise identity is the deterministic ingredient of finite-grid compensated martingale cell decompositions.
-- source:
--   W7-06 original X.X future-grid telescoping for L² cell decomposition, no auxiliary process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_consecutive_future_increment_additivity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s u v : ℝ≥0) :
    X.X (s + u + v) ω - X.X s ω =
      (X.X (s + u) ω - X.X s ω) +
      (X.X (s + u + v) ω - X.X (s + u) ω) := by sorry
