-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a26_terminal_strict_stop_eventually_zero
-- name    : AvramDividend.Classical.avram_ga_a26_terminal_strict_stop_eventually_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T08:31:56.242069+00:00
-- url     : https://prove2.me/theorems/8d5bcb4a-48ee-48e8-b720-3a57de90f873
-- title:
--   Original stopped terminal spatial increment eventually vanishes for every strict pre-horizon stopping path
-- statement:
--   For any sample path with stopping time strictly before horizon n, eventually both final mesh endpoints are clipped at the stop and the exact terminal spatial increment vanishes. This proves the strict-stop branch of the terminal Gaussian almost-sure limit.
-- source:
--   Avram Gaussian A26 strict-stop terminal convergence

import Mathlib
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a26_terminal_strict_stop_eventually_zero
    {Ω : Type*} (L D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (x : ℝ) (n : ℝ≥0) (ρ : Ω → ℝ≥0) (ω : Ω)
    (hr : ρ ω < n) :
    ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      let Δ : ℝ≥0 := n / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
      w (x + L (v (m + 1)) ω - D (v m) ω) -
        w (x + L (v m) ω - D (v m) ω) = 0 := by sorry
