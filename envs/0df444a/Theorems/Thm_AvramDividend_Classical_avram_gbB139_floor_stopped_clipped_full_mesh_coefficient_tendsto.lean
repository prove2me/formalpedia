-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB139_floor_stopped_clipped_full_mesh_coefficient_tendsto
-- name    : AvramDividend.Classical.avram_gbB139_floor_stopped_clipped_full_mesh_coefficient_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T08:53:16.896838+00:00
-- url     : https://prove2.me/theorems/b63c958e-dc1e-4c89-b5b7-ab6eb6a89423
-- title:
--   Original full finite mesh stopped clipped coefficient converges at good physical times
-- statement:
--   The Proved B111 uniform-cell identity converts the full finite-step sum into the coefficient sampled at the floor-selected mesh left endpoint. The Proved B113 continuity result yields its limit, retaining strict stopping and clipping. This is the original-mesh deterministic convergence step for B102 at good times.
-- source:
--   Proved B111 and B113

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB113_floor_stopped_clipped_coefficient_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_gbB111_uniform_cell_step_sum_eq_floor_coefficient
open Filter Topology Set AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_gbB139_floor_stopped_clipped_full_mesh_coefficient_tendsto
    (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) (n : ℝ))
    (q : ℝ) (w : ℝ → ℝ) (a b : ℝ)
    (Y : ℝ → ℝ) (hY : ContinuousAt Y t)
    (hCont : Y t ∈ Ioo a b → ContinuousAt (deriv w) (Y t))
    (ha : Y t ≠ a) (hb : Y t ≠ b)
    (ρ : ℝ) (hρ : t ≠ ρ) :
    let K : ℕ → ℝ := fun m =>
      let Δ : ℝ := (n : ℝ) / ((m : ℝ) + 1)
      (Finset.range (m + 1)).sum (fun i =>
        let s : ℝ := (i : ℝ) * Δ
        if s ≤ t ∧ t < (((i + 1 : ℕ) : ℝ) * Δ) then
          if s < ρ then Real.exp (-(q * s)) *
            (if Y s ∈ Icc a b then deriv w (Y s) else 1)
          else 0 else 0)
    Tendsto K atTop (𝓝 (if t < ρ then
      Real.exp (-(q * t)) *
        (if Y t ∈ Icc a b then deriv w (Y t) else 1)
      else 0)) := by sorry
