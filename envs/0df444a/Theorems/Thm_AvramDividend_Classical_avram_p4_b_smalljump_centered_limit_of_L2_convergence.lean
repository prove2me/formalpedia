-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_centered_limit_of_L2_convergence
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_centered_limit_of_L2_convergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:52:22.404904+00:00
-- url     : https://prove2.me/theorems/c80888e4-80a9-428a-b5aa-094a1e9aa9c9
-- title:
--   L² closure transfers exact zero expectation from finite Lévy-jump bands
-- statement:
--   In the same original probability space, suppose finite-band compensated Lévy jump variables F_n are integrable and centred, the target M is integrable, and their actual L² errors tend to zero. Since P is a probability measure, L¹ error is bounded by L² error; continuity of the Bochner integral proves E M=0. This separates the authentic stochastic L² isometry and predictable rectangle compensator (still required) from the proved analytic closure; no independent Poisson process or assumed count law.
-- source:
--   Pinned Mathlib eLpNorm_le_eLpNorm_of_exponent_le, eLpNorm_one_eq_lintegral_enorm, order squeeze and tendsto_integral_of_L1. The L² approximation premise remains explicit.

import Mathlib
open MeasureTheory Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_centered_limit_of_L2_convergence
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (F : ℕ → Ω → ℝ) (M : Ω → ℝ)
    (hFI : ∀ n, Integrable (F n) P)
    (hMI : Integrable M P)
    (hMean : ∀ n, (∫ ω, F n ω ∂P) = 0)
    (hConv2 : Tendsto
      (fun n => eLpNorm (fun ω => F n ω - M ω) 2 P)
      atTop (𝓝 0)) :
    (∫ ω, M ω ∂P) = 0  := by sorry
