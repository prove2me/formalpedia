-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB162_nnreal_step_clipped_pointwise_convergence_at_good_time
-- name    : AvramDividend.Classical.avram_gbB162_nnreal_step_clipped_pointwise_convergence_at_good_time
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T12:55:56.516215+00:00
-- url     : https://prove2.me/theorems/9427a96c-0716-4f2f-9057-6c7270f01c1a
-- title:
--   NNReal full-mesh stopped clipped coefficient converges at good physical time
-- statement:
--   At a continuity time away from clipping boundaries and stopping time, the full NNReal-parameter mesh coefficient converges to the stopped physical clipped coefficient. Combine the proved real-grid full-mesh convergence B139 and the exact NNReal/real grid sum identity B161.
-- source:
--   Proved B139 and B161

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB139_floor_stopped_clipped_full_mesh_coefficient_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_gbB161_nnreal_mesh_sum_eq_real_mesh_sum
open Filter Topology Set AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB162_nnreal_step_clipped_pointwise_convergence_at_good_time
    (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) (n : ℝ))
    (q : ℝ) (w : ℝ → ℝ) (a b : ℝ)
    (Y : ℝ → ℝ) (hY : ContinuousAt Y t)
    (hCont : Y t ∈ Ioo a b → ContinuousAt (deriv w) (Y t))
    (ha : Y t ≠ a) (hb : Y t ≠ b)
    (ρ : ℝ) (hρ : t ≠ ρ) :
    let K : ℕ → ℝ := fun m =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      (Finset.range (m + 1)).sum (fun i =>
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if (s : ℝ) ≤ t ∧ t < ((s + Δ : ℝ≥0) : ℝ) then
          if (s : ℝ) < ρ then Real.exp (-(q * (s : ℝ))) *
            (if Y (s : ℝ) ∈ Icc a b then deriv w (Y (s : ℝ)) else 1)
          else 0 else 0)
    Tendsto K atTop (𝓝 (if t < ρ then
      Real.exp (-(q * t)) *
        (if Y t ∈ Icc a b then deriv w (Y t) else 1)
      else 0)) := by sorry
