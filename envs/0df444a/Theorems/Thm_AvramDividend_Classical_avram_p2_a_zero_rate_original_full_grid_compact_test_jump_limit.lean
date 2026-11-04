-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_full_grid_compact_test_jump_limit
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_original_full_grid_compact_test_jump_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:57:58.444592+00:00
-- url     : https://prove2.me/theorems/cb482355-5c38-4376-8961-2245206ccc29
-- title:
--   Original cadlag full-mesh compact-test sum tends to finite genuine jump sum
-- statement:
--   A source-faithful deterministic finite-jump matching theorem for original càdlàg sample paths: complete mesh compact-test sums converge to genuine jump-test sums if each true jump has a unique selected cell and its selected mark converges. The proof derives vanishing contributions from nonselected cells via the proved reverse large-cell theorem and then applies finite sum convergence. This is the pathwise part of the original Lévy rate proof, with no compensator assumption.

import Mathlib
open Filter Set Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_original_full_grid_compact_test_jump_limit
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0)
    (a b : ℕ → ℕ → ℝ≥0) (w : ℕ → ℝ≥0)
    (haT : ∀ n i, a n i ≤ T)
    (hab : ∀ n i, a n i ≤ b n i)
    (hbw : ∀ n i, b n i ≤ a n i + w n)
    (hw : Tendsto w atTop (𝓝 (0 : ℝ≥0)))
    (hL : ∀ t : ℝ≥0,
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t : ℝ≥0, ContinuousWithinAt Y (Ici t) t)
    (ρ : ℝ) (hρ : 0 < ρ)
    (F : Finset ℝ≥0)
    (hF : ∀ t ∈ Icc (0 : ℝ≥0) T,
      ρ ≤ |Y t - Function.leftLim Y t| → t ∈ F)
    (grid : ℕ → Finset ℕ) (idx : ℝ≥0 → ℕ → ℕ)
    (hinside : ∀ n, ∀ t ∈ F, idx t n ∈ grid n)
    (hinj : ∀ᶠ n : ℕ in atTop,
      Set.InjOn (fun t => idx t n) (F : Set ℝ≥0))
    (hunique : ∀ n i, ∀ t ∈ F,
      a n i < t ∧ t ≤ b n i → i = idx t n)
    (hselected : ∀ t ∈ F,
      Tendsto (fun n => Y (b n (idx t n)) - Y (a n (idx t n)))
        atTop (𝓝 (Y t - Function.leftLim Y t)))
    (f : ℝ → ℝ) (hf : Continuous f)
    (hvanish : ∀ z : ℝ, |z| < ρ → f z = 0) :
    Tendsto (fun n => ∑ i ∈ grid n, f (Y (b n i) - Y (a n i)))
      atTop (𝓝 (∑ t ∈ F, f (Y t - Function.leftLim Y t)))  := by sorry
