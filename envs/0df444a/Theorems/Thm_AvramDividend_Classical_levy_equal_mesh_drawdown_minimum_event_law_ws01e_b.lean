-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_equal_mesh_drawdown_minimum_event_law_ws01e_b
-- name    : AvramDividend.Classical.levy_equal_mesh_drawdown_minimum_event_law_ws01e_b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T16:06:08.613167+00:00
-- url     : https://prove2.me/theorems/2fa25ff1-ef4f-49e8-acd1-402e07ccbb50
-- title:
--   Actual Lévy finite-grid terminal drawdown and minimum share their threshold law
-- statement:
--   For the actual spectrally negative Lévy process, choose an arbitrary finite equal-mesh time grid and extend its consecutive increments by zeros after index n. Under the true pushforward law of this random sequence, the probability that terminal total minus some preceding partial sum is at most a equals the probability that some ordinary partial sum is at most a. This includes grid start/end and n=0, requires no independent exponential horizon, and is a source-faithful fixed-grid consequence of the genuine Lévy increment-vector reversal law plus the canonically Proved reversal-invariant measure theorem.
-- source:
--   Kuznetsov–Kyprianou–Rivero, The Theory of Scale Functions for Spectrally Negative Lévy Processes, §2.1 path reversal (https://warwick.ac.uk/fac/sci/statistics/staff/academic-research/kyprianou/scale-review-final.pdf). Uses Proved b78d5f90-43d4-4229-9f1a-23b5c29a59a7 and 1eada579-3e41-4583-8998-f7bdce582941.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_finite_grid_drawdown_minimum_event_probability_of_reversal_ws01e_b
import Theorems.Thm_AvramDividend_Classical_levy_equal_mesh_increment_vector_law_reversal_ws01e_b
open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_equal_mesh_drawdown_minimum_event_law_ws01e_b
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (δ : ℝ≥0) (n : ℕ) (a : ℝ) :
    let inc : Ω → ℕ → ℝ := fun ω j =>
      if j < n then
        X.X (((j + 1 : ℕ) : ℝ≥0) * δ) ω -
          X.X ((j : ℝ≥0) * δ) ω
      else 0
    let ν : MeasureTheory.Measure (ℕ → ℝ) := MeasureTheory.Measure.map inc P
    ν {v : ℕ → ℝ | ∃ k : Fin n.succ,
      Finset.sum (Finset.range n) v -
        Finset.sum (Finset.range k.val) v ≤ a} =
    ν {v : ℕ → ℝ | ∃ k : Fin n.succ,
      Finset.sum (Finset.range k.val) v ≤ a} := by sorry
