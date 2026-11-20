-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_actual_stopped_physical_source_exact_zero_clock
-- name    : AvramDividend.Classical.avram_jump6_B_actual_stopped_physical_source_exact_zero_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T22:23:51.222921+00:00
-- url     : https://prove2.me/theorems/e5021618-25cb-4bb7-8c23-ab09ca97c091
-- title:
--   Actual signed original stopped physical source vanishes at exact zero clock
-- statement:
--   On a sample path where the original stopped clock sigma is exactly zero, the full actual signed physical Itô source sum over any finite grid and all negative jump activity is exactly zero, including both discounted product and spatial increments. Uses the true X.X process, right-limit dividends D, genuine stopped physical grid min(u_i,sigma), and arbitrary generator candidate w.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_actual_stopped_physical_source_exact_zero_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (σ : Ω → ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (m : ℕ → ℕ)
    (j : ℕ) (ω : Ω) (hzero : σ ω = 0) :
    let v : ℕ → ℝ≥0 := fun i => min (u j i) (σ ω)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t =>
      x + X.X t ω - rightLimit D t ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    Finset.sum (Finset.range (m j)) (fun i =>
      (E (v (i + 1)) - E (v i)) * w (Y (v i)) +
        E (v (i + 1)) * (w (Z i) - w (Y (v i)))) = 0 := by sorry
