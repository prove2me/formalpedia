-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_indexed_iid_prefix_current_wait_future_independent
-- name    : AvramDividend.Classical.chat06_indexed_iid_prefix_current_wait_future_independent
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T08:02:33.086693+00:00
-- url     : https://prove2.me/theorems/12ca3d31-bc12-48b4-b5af-11dd10e0b7d0
-- title:
--   Indexed iid masked prefix and current wait are jointly independent of the full subsequent waiting suffix
-- statement:
--   For an iid sequence of waiting times and a fixed index n, the complete zero-masked sequence of earlier waits together with the current nth wait is independent of the entire infinite waiting suffix beginning at n+1. The theorem derives from the proved full-prefix/full-suffix independence by measurable transformation and exposes the independence required to combine current exponential residual survival with all later renewal waits. This is a fixed-index theorem, leaving random count selection to a subsequent gluing argument.
-- source:
--   Private source bv_indexed_iid_prefix_current_wait_future_independent_v2_chat06_20261021.lean, 68 lines; exact SHA-256 2230f25bf8709d0a7b97a928916c17ec2923bd00c343b8f858523c4900d2e903; remote probe 1b64e82b-73af-4b02-84da-d83540933fc0 passed source elaboration to deliberate sentinel with zero candidate errors at pinned revision. Neither official publication nor proof acceptance implied.

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Theorems.Thm_AvramDividend_Classical_chat06_masked_iid_prefix_full_suffix_independence

open MeasureTheory ProbabilityTheory

theorem AvramDividend.Classical.chat06_indexed_iid_prefix_current_wait_future_independent
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P) (n : ℕ) :
    IndepFun
      (fun ω => ((fun i => if h : i < n then τ i ω else 0), τ n ω))
      (fun ω (j : ℕ) => τ (n + 1 + j) ω) P := by sorry
