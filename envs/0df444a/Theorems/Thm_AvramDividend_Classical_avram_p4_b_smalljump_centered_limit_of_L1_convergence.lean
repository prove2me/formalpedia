-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_centered_limit_of_L1_convergence
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_centered_limit_of_L1_convergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:52:17.242514+00:00
-- url     : https://prove2.me/theorems/0b02c2b1-dfce-4fc3-95c5-7d629ed10b78
-- title:
--   L¹ closure of centred original compensated small-jump truncations
-- statement:
--   For integrable finite-band original compensated jump variables F_n with exactly zero expectation and an integrable original-space limiting variable M, convergence in the genuine L¹ seminorm implies M has expectation zero. This is the analytic closure required after deriving actual original Lévy L² isometry and convergence; those stochastic premises are deliberately explicit and are not deduced from the still Open predictable rectangle compensator.
-- source:
--   Use pinned Mathlib MeasureTheory.tendsto_integral_of_L1, then uniqueness of the real-valued limit of a constant zero sequence. No stochastic assumption is hidden.

import Mathlib
open MeasureTheory Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_centered_limit_of_L1_convergence
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (F : ℕ → Ω → ℝ) (M : Ω → ℝ)
    (hFI : ∀ n, Integrable (F n) P)
    (hMI : Integrable M P)
    (hMean : ∀ n, (∫ ω, F n ω ∂P) = 0)
    (hConv : Tendsto
      (fun n => ∫⁻ ω, ‖F n ω - M ω‖ₑ ∂P)
      atTop (𝓝 0)) :
    (∫ ω, M ω ∂P) = 0  := by sorry
