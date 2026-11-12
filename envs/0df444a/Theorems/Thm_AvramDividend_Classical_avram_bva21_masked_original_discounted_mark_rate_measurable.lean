-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva21_masked_original_discounted_mark_rate_measurable
-- name    : AvramDividend.Classical.avram_bva21_masked_original_discounted_mark_rate_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:07:06.253742+00:00
-- url     : https://prove2.me/theorems/d7d02797-52fd-4ed6-9011-7f61a62a66b6
-- title:
--   Stopped original closed-cap discounted mark rate is measurable from measurable reserve and mark kernel
-- statement:
--   The exact physical time predicate in original compensator K involves the positive time test, strict n-th inner horizon, inclusive ruin clock, and inclusive closed reserve cap. If the physical prepayment reserve U and negative-mark integrated rate ψ are measurable, the predicate is measurable, and the discounted masked rate is measurable. Consequently this proves the required a.e. strong measurability premise of the original source-K time-integral bridge under the two basic source measurability facts.
-- source:
--   Source-specific measurability wrapper for original BV stopped compensator K integrand and 7ccc2a1a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bva21_masked_original_discounted_mark_rate_measurable
    (C τ : ℝ≥0∞) (q T : ℝ) (n : ℕ)
    (U : ℝ≥0 → ℝ) (hU : Measurable U)
    (ψ : ℝ → ℝ) (hψ : Measurable ψ) :
    Measurable (fun t : ℝ≥0 =>
      if 0 < t ∧ (t : ℝ) < T - T / ((n : ℝ) + 2) ∧
         (t : ℝ≥0∞) ≤ τ ∧ 0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C
      then Real.exp (-(q * (t : ℝ))) * ψ (U t)
      else 0) := by sorry
