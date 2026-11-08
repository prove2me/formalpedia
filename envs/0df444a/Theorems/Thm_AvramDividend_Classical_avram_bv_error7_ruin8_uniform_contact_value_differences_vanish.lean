-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_uniform_contact_value_differences_vanish
-- name    : AvramDividend.Classical.avram_bv_error7_ruin8_uniform_contact_value_differences_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T08:51:19.989504+00:00
-- url     : https://prove2.me/theorems/d1c21362-b501-4a33-b230-4b47b15601b8
-- title:
--   Uniformly continuous values absorb shrinking sample-dependent contact increments without a derivative bound
-- statement:
--   For a uniformly continuous value on a set containing both sample-dependent contact endpoints, any sequence of increments tending to zero has vanishing value change even when the base reserve does not converge. This supplies the analytic derivative-free alternative for the authentic BV ruin contact cell.
-- source:
--   Apply the metric epsilon-delta definition of uniform continuity to the pair z_m and z_m+c_m. Since their distance is |c_m| and c_m→0, their value difference tends to zero. No derivative, stochastic process substitution, or expectation-convergence inference occurs in this child.

import Mathlib
open MeasureTheory Set Filter
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_ruin8_uniform_contact_value_differences_vanish
    (w : ℝ → ℝ) (s : Set ℝ) (hw : UniformContinuousOn w s)
    (z c : ℕ → ℝ)
    (hz : ∀ m, z m ∈ s) (hzc : ∀ m, z m + c m ∈ s)
    (hc : Tendsto c atTop (nhds (0 : ℝ))) :
    Tendsto (fun m => w (z m + c m) - w (z m))
      atTop (nhds (0 : ℝ)) := by sorry
