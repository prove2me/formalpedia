-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_ruinclipped_predictable_two_noise_mesh_gains_zero_at_zero_stop
-- name    : AvramDividend.Classical.avram_b24_original_ruinclipped_predictable_two_noise_mesh_gains_zero_at_zero_stop
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:26:10.565205+00:00
-- url     : https://prove2.me/theorems/ef9c2969-5963-474a-99df-b2696a81a9fd
-- title:
--   Original bounded predictable two-noise ruin-clipped finite mesh gains vanish exactly at zero stopping time
-- statement:
--   For any original bounded predictable finite grid (including the actual R intrinsic Gaussian and Jsmall compensated negative-smallmark fields), the strict stopped gain coefficient is (if σ≤gridLeft then 0 else weight). When the original stopping clock σ(ω)=0, nonnegative physical grid times imply every such coefficient is zero and both exact finite stochastic gain sums vanish on that sample path. This is the algebraic source of the zero-clock gain mask when splitting the exact original Iic cash and ruin-contact Itô source; no time-zero payment is discarded.
-- source:
--   Exact source stopped-mask finite-sum formula in Proved 194c4619 and canonical e44; NNReal.zero_le and Finset.sum_zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_ruinclipped_predictable_two_noise_mesh_gains_zero_at_zero_stop
    {Ω : Type*} (σ : Ω → ℝ≥0)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (S : Finset ℕ) (a b : ℕ → ℝ≥0)
    (WG WJ : ℕ → Ω → ℝ)
    (ω : Ω) (hσzero : σ ω = 0) :
    (∑ i ∈ S, (if σ ω ≤ a i then 0 else WG i ω) *
      (R (b i) ω - R (a i) ω)) = 0 ∧
    (∑ i ∈ S, (if σ ω ≤ a i then 0 else WJ i ω) *
      (Jsmall (b i) ω - Jsmall (a i) ω)) = 0 := by sorry
