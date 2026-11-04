-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_stopped_clock_support_from_tau_bound
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_stopped_clock_support_from_tau_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:24:40.380044+00:00
-- url     : https://prove2.me/theorems/42adaadb-e16d-47d4-85e8-f112107663f9
-- title:
--   Exact physical stopped jump kernel has automatic finite-horizon support
-- statement:
--   For the actual stopped kernel at a pathwise bounded clock τ≤T, prove the kernel's extension by zero outside the finite physical horizon is its own restriction, including exact ≤ boundary behaviour. This is a deterministic support interface needed in the original Ω,P,𝓕/X/D stopped signed jump expectation theorem and introduces no independent jump or compensator axiom.
-- source:
--   Existing accepted 4846bbef stopped source signed L1 theorem hSupport premise

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_stopped_clock_support_from_tau_bound
    {Ω : Type*} (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτBound : ∀ ω, τ ω ≤ T)
    (G H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hH : H = fun p =>
      if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0) :
    ({p : ((ℝ≥0 × Ω) × ℝ) | p.1.1 ≤ T} : Set _).indicator H = H := by sorry
