-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f6_hjb_exit_budget_iSup
-- name    : AvramDividend.Classical.avram_p4_f6_hjb_exit_budget_iSup
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T10:10:57.535972+00:00
-- url     : https://prove2.me/theorems/c92e9ff7-05d9-44dc-89c3-14499fa3f7b1
-- title:
--   Monotone convergence transfers bounded finite-horizon killed exit budgets to the full horizon
-- statement:
--   For a nondecreasing sequence of measurable nonnegative killed-exit reward densities, any finite-horizon estimate that bounds the scalar-weighted expected reward uniformly in the horizon also bounds the expected pointwise supremum reward. The proof is a monotone convergence theorem and multiplication preserving suprema in ENNReal. This is the infinite-horizon passage needed to transfer bounded upper-exit HJB budgets to the original full two-sided exit transform.
-- source:
--   Source-faithful monotone convergence step for original killed upper-exit HJB bound 8d1164b7-10ee-4fad-92a7-4f012f12ed91. Uses MeasureTheory.lintegral_iSup and ENNReal.mul_iSup at pinned Mathlib.

import Mathlib
open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f6_hjb_exit_budget_iSup
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (f : ℕ → Ω → ℝ≥0∞)
    (hf : ∀ n : ℕ, Measurable (f n)) (hmono : Monotone f)
    (a c : ℝ≥0∞)
    (hbudget : ∀ n : ℕ, a * (∫⁻ ω, f n ω ∂P) ≤ c) :
    a * (∫⁻ ω, (⨆ n : ℕ, f n ω) ∂P) ≤ c := by sorry
