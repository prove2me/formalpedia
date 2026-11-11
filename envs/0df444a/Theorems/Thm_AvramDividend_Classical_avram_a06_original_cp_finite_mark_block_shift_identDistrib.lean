-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_finite_mark_block_shift_identDistrib
-- name    : AvramDividend.Classical.avram_a06_original_cp_finite_mark_block_shift_identDistrib
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T02:47:37.451572+00:00
-- url     : https://prove2.me/theorems/8bec7251-77ca-4152-b0f2-ee185a4c0e06
-- title:
--   Original compound-Poisson marked sums of deterministic length are invariant under deterministic mark-index shifts
-- statement:
--   The sum of any fixed number of consecutive original compound-Poisson iid marks has the same distribution whether taken from the start or after any deterministic integer shift. This supplies the finite-block conditioning step in A06 marked-band stationary increments.
-- source:
--   Use the source-exact full iid mark stream shift IdentDistrib 75627888 and compose both streams with the measurable map summing the first n coordinates. The finite coordinate sum is measurable by Finset.measurable_sum and measurable_pi_apply.

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_mark_stream_shift_identDistrib
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_cp_finite_mark_block_shift_identDistrib
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (m n : ℕ) :
    IdentDistrib (fun ω => ∑ j ∈ Finset.range n, Y (m + j) ω)
      (fun ω => ∑ j ∈ Finset.range n, Y j ω) P P := by sorry
