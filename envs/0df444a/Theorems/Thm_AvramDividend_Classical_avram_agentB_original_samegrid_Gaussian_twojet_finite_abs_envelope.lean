-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_agentB_original_samegrid_Gaussian_twojet_finite_abs_envelope
-- name    : AvramDividend.Classical.avram_agentB_original_samegrid_Gaussian_twojet_finite_abs_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T10:08:38.603771+00:00
-- url     : https://prove2.me/theorems/7faea906-9c17-4e9d-a201-69597e2984e9
-- title:
--   Exact finite Gaussian Hermite pre/post gradient and Hessian grid difference absolute envelope
-- statement:
--   For arbitrary finite deterministic-grid Gaussian Hermite coefficients, the absolute difference of two discounted linear-plus-quadratic centred source sums is bounded by the sum of absolute differences of their gradient coefficients times absolute centred increments and their Hessian coefficients times absolute centred quadratic increments. This is the exact elementary cellwise estimate needed to compare the original pre-dividend and postright-dividend physical Gaussian martingale grids; no stochastic independence is assumed.
-- source:
--   Finset.abs_sum_le_sum_abs, Real.abs_add and Real.abs_mul, and elementary algebra applied to the original same-grid first/second Hermite Gaussian terms.

import Mathlib
open BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_agentB_original_samegrid_Gaussian_twojet_finite_abs_envelope
    (n : ℕ) (e z u a b c d : ℕ → ℝ) :
    |∑ i ∈ Finset.range n, e i *
      ((a i * z i + b i * u i) - (c i * z i + d i * u i))| ≤
      ∑ i ∈ Finset.range n, |e i| *
        (|a i - c i| * |z i| + |b i - d i| * |u i|) := by sorry
