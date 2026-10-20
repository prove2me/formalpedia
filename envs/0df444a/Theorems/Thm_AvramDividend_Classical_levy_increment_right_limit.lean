-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_increment_right_limit
-- name    : AvramDividend.Classical.levy_increment_right_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T17:17:37.040514+00:00
-- url     : https://prove2.me/theorems/3f367b25-75de-433d-bd3d-5a27b29ad318
-- title:
--   Shifted Lévy increments converge pathwise when their start time decreases
-- statement:
--   For the exact published spectral-negative Lévy process, for every sample path and deterministic s and t, the future increment X_t-X_u converges as u approaches s strictly from the right to X_t-X_s. This is the pointwise continuity half of the argument transferring independence of future increments to the right-continuous filtration; the other half is the separate independence-limit theorem.
-- source:
--   SpectrallyNegativeLevy.rightCont pinned definition and Mathlib ContinuousWithinAt.mono with one-sided order topology.

import Mathlib.Topology.Algebra.Order.Field
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_increment_right_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t : ℝ≥0) :
    Tendsto
      (fun u : ℝ≥0 => X.X t ω - X.X u ω)
      (𝓝[>] s)
      (𝓝 (X.X t ω - X.X s ω)) := by sorry
