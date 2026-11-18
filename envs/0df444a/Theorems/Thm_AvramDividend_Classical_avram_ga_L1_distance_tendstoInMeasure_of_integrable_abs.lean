-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_L1_distance_tendstoInMeasure_of_integrable_abs
-- name    : AvramDividend.Classical.avram_ga_L1_distance_tendstoInMeasure_of_integrable_abs
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T17:55:27.987245+00:00
-- url     : https://prove2.me/theorems/a00c2248-209d-4c99-a233-003be92905e8
-- title:
--   Analytic L1 convergence implies convergence in measure
-- statement:
--   If integrable L1 absolute error tends to zero, the approximants converge in measure, with no measurability assumption for the limit.

import Mathlib
open MeasureTheory Filter Topology

theorem AvramDividend.Classical.avram_ga_L1_distance_tendstoInMeasure_of_integrable_abs {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (M : ℕ → Ω → ℝ) (Z : Ω → ℝ) (hDiff : ∀ m, Integrable (fun ω => |Z ω - M m ω|) μ) (hLim : Tendsto (fun m => ∫ ω, |Z ω - M m ω| ∂μ) atTop (nhds (0 : ℝ))) : TendstoInMeasure μ M atTop Z := by sorry
