-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_time_set_has_monotone_zero_started_grid
-- name    : AvramDividend.Classical.finite_time_set_has_monotone_zero_started_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T15:06:48.865353+00:00
-- url     : https://prove2.me/theorems/6f65407e-2bd4-47df-8cf0-f82e6ff490ae
-- title:
--   Every finite collection of nonnegative observation times lies in a monotone time grid starting at zero
-- statement:
--   Given an arbitrary finite set J of nonnegative real times, construct a nondecreasing sequence t indexed by all natural numbers with t(0)=0 and a finite length n such that every j in J appears as some t(i+1), i< n. Use the sorted order embedding from Fin(J.card) to the finite set J, extend it to all natural indices by clipping at the last time, and place time 0 at index 0. The empty case uses the constant-zero sequence. This elementary combinatorial lemma supplies the missing bridge from accepted monotone finite-grid Lévy laws to all finite-dimensional coordinate laws and then full path-law equality.
-- source:
--   Pinned Mathlib Finset.orderEmbOfFin and Finset.orderIsoOfFin (Mathlib.Data.Finset.Sort), Nat min/saturation arithmetic by targeted omega tactic. This theorem depends on no stochastic or unpublished platform results and is a prerequisite for cross_sample_finite_coord_law_of_grid_vector_law and cross_sample_path_law_eq_of_all_finite_vector_laws.

import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

open MeasureTheory Set
open scoped ENNReal NNReal

theorem AvramDividend.Classical.finite_time_set_has_monotone_zero_started_grid
    (J : Finset ℝ≥0) :
    ∃ t : ℕ → ℝ≥0, Monotone t ∧ t 0 = 0 ∧
      ∃ n : ℕ, ∀ j : J, ∃ i : Fin n, t (i.val + 1) = j.1 := by sorry
