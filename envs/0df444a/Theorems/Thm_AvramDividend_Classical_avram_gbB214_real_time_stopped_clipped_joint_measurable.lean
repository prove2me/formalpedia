-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB214_real_time_stopped_clipped_joint_measurable
-- name    : AvramDividend.Classical.avram_gbB214_real_time_stopped_clipped_joint_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:14:59.213713+00:00
-- url     : https://prove2.me/theorems/edd8a333-8bfa-4ad5-8f04-a25de021f5be
-- title:
--   Real-time stopped discounted clipped source coefficient is jointly measurable
-- statement:
--   For jointly measurable nonnegative-time state paths, a measurable random horizon and a measurable spatial clip, the physical real-time strictly pre-stop discounted coefficient is jointly measurable.
-- source:
--   Gaussian B original selected physical L2 B207, exact measurable limit when t is compared as real directly with stop horizon rho; complements B209.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB214_real_time_stopped_clipped_joint_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (Y : ℝ≥0 → Ω → ℝ)
    (hY : Measurable (fun z : ℝ≥0 × Ω => Y z.1 z.2))
    (ρ : Ω → ℝ≥0) (hρ : Measurable ρ)
    (g : ℝ → ℝ) (hg : Measurable g) (q : ℝ) :
    Measurable (fun z : ℝ × Ω =>
      if z.1 < (ρ z.2 : ℝ) then
        Real.exp (-(q * z.1)) * g (Y (Real.toNNReal z.1) z.2)
      else 0) := by sorry
