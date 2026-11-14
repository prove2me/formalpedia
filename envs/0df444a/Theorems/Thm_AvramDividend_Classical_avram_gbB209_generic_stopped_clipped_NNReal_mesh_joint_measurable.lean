-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB209_generic_stopped_clipped_NNReal_mesh_joint_measurable
-- name    : AvramDividend.Classical.avram_gbB209_generic_stopped_clipped_NNReal_mesh_joint_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:12:44.871697+00:00
-- url     : https://prove2.me/theorems/1ee2114c-9ac3-4dc4-9304-37de57646407
-- title:
--   Joint measurability of stopped clipped NNReal grid and physical-time limit
-- statement:
--   A jointly measurable nonnegative-time state and a measurable random stopping horizon and spatial clipping function yield jointly measurable finite-grid stopped discounted coefficients and physical-time limiting coefficient.
-- source:
--   Original Gaussian B countable selected clipping physical L2: discharges structural joint measurability using B_wave8_20 and B211.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB209_generic_stopped_clipped_NNReal_mesh_joint_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (Y : ℝ≥0 → Ω → ℝ)
    (hY : Measurable (fun z : ℝ≥0 × Ω => Y z.1 z.2))
    (ρ : Ω → ℝ≥0) (hρ : Measurable ρ)
    (g : ℝ → ℝ) (hg : Measurable g)
    (q : ℝ) (n : ℕ) :
    let F : ℝ≥0 → Ω → ℝ := fun s ω =>
      if s < ρ ω then Real.exp (-(q * (s : ℝ))) * g (Y s ω) else 0
    let K : ℕ → ℝ → Ω → ℝ := fun m t ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      (Finset.range (m + 1)).sum (fun i =>
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if (s : ℝ) ≤ t ∧ t < ((s + Δ : ℝ≥0) : ℝ)
        then F s ω else 0)
    let H : ℝ → Ω → ℝ := fun t ω =>
      if Real.toNNReal t < ρ ω then
        Real.exp (-(q * t)) * g (Y (Real.toNNReal t) ω)
      else 0
    (∀ m, Measurable (fun z : ℝ × Ω => K m z.1 z.2)) ∧
    Measurable (fun z : ℝ × Ω => H z.1 z.2) := by sorry
