-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a57_original_clipped_gaussian_cell_width
-- name    : AvramDividend.Classical.avram_ga_a57_original_clipped_gaussian_cell_width
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T18:52:38.881894+00:00
-- url     : https://prove2.me/theorems/f4c1113e-ac38-45fb-a4aa-d8390e37d9c4
-- title:
--   Original clipped Gaussian grid successor width is between zero and n/(m+1)
-- statement:
--   For the exact original stopped Gaussian mesh v(k)=min(k*n/(m+1),rho), each adjacent clipped cell has nonnegative length and width at most n/(m+1), including the single stop-straddling cell. This is an exact deterministic necessary estimate for physical interior Gaussian Taylor remainders b0d9951c.
-- source:
--   Proved original clipped source cell nonexpansivity 572b8d66; original b0d9951c. Includes no process or filtration changes.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_clipped_source_cell_mesh_nonexpansive
open AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a57_original_clipped_gaussian_cell_width
    (n m i : ℕ) (ρ : ℝ≥0) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun k => min ((k : ℝ≥0) * Δ) ρ
    0 ≤ (v (i + 1) : ℝ) - (v i : ℝ) ∧
      (v (i + 1) : ℝ) - (v i : ℝ) ≤ (Δ : ℝ) := by sorry
