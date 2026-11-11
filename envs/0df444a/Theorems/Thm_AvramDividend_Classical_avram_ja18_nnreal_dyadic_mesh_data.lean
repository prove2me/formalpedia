-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_nnreal_dyadic_mesh_data
-- name    : AvramDividend.Classical.avram_ja18_nnreal_dyadic_mesh_data
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T21:49:09.070117+00:00
-- url     : https://prove2.me/theorems/d9aa5a62-7abe-4d9f-b7a7-9bf443f1081e
-- title:
--   Dyadic nonnegative-real mesh certificate of arbitrary exact integer horizon
-- statement:
--   For any integer horizon n, define e_k(i)=i/2^k, N_k=n*2^k, δ_k=1/2^k. Prove monotonicity, e_k(0)=0, uniform one-step bound, e_k(N_k)=n and δk→0. Entirely elementary NNReal arithmetic and the pinned Mathlib geometric-power convergence.
-- source:
--   Deterministic arithmetic child for 40599988, independent of original process. Complements generic stochastic-clock child.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_nnreal_dyadic_mesh_data
    (n : ℕ) :
    ∃ (e : ℕ → ℕ → ℝ≥0) (N : ℕ → ℕ) (δ : ℕ → ℝ≥0),
      (∀ k, Monotone (e k)) ∧
      (∀ k, e k 0 = 0) ∧
      (∀ k i, e k (i + 1) ≤ e k i + δ k) ∧
      (∀ k, e k (N k) = (n : ℝ≥0)) ∧
      Tendsto δ atTop (𝓝 0) := by sorry
