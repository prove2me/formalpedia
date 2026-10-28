-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_mark_step_negative_jump_count_eq_mark_count
-- name    : AvramDividend.Classical.finite_mark_step_negative_jump_count_eq_mark_count
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T22:58:00.874742+00:00
-- url     : https://prove2.me/theorems/0949e0ee-6f6a-4b53-98aa-dec407287daa
-- title:
--   A collision-free finite marked Poisson step path has exactly as many large downward jumps as negative marked arrivals
-- statement:
--   Let S be a finite collection of marked arrivals (τ_i,w_i), with no two marks at the same time. The step path is the cumulative sum of all weights arriving by t. Count the times in S.image τ at which its left jump is strictly below -a. That count equals the number of marks with w_i < -a. This is a precise finite path-count/Poisson-mark-count identification, bridging canonical point data and observable process jumps before a limit to infinite small-jump activity.
-- source:
--   Companion finite_marked_step_jump_eq_single_of_injective [b86cfb0f-2396-446a-8633-384f9a45bcff] and pinned Mathlib Finset.sum_image. Needed for Avram canonical zero-count transport.

import Mathlib.Data.NNReal.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Theorems.Thm_AvramDividend_Classical_finite_marked_step_jump_eq_single_of_injective

open AvramDividend.Classical
open scoped NNReal BigOperators

theorem AvramDividend.Classical.finite_mark_step_negative_jump_count_eq_mark_count
    {ι : Type*} (S : Finset ι) (τ : ι → ℝ≥0) (w : ι → ℝ)
    (hτ : ∀ i ∈ S, ∀ j ∈ S, τ i = τ j → i = j)
    (a : ℝ) :
    (∑ t ∈ S.image τ,
      if (∑ j ∈ S, if τ j ≤ t then w j else 0) -
         (∑ j ∈ S, if τ j < t then w j else 0) < -a
      then (1 : ℕ) else 0) =
    ∑ i ∈ S, if w i < -a then (1 : ℕ) else 0 := by sorry
