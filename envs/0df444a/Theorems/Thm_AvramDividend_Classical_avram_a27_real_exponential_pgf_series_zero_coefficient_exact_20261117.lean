-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_real_exponential_pgf_series_zero_coefficient_exact_20261117
-- name    : AvramDividend.Classical.avram_a27_real_exponential_pgf_series_zero_coefficient_exact_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T19:01:17.187086+00:00
-- url     : https://prove2.me/theorems/c807d50e-e824-4db8-b2ef-728e238ee118
-- title:
--   The constant coefficient of a real exponential PGF equals its zero-argument exponential
-- statement:
--   If sum z^k Ck=exp(qz-r) on the unit interval, then evaluating at z=0 gives C0=exp(-r). This is the exact first coefficient for the analytic count-cell uniqueness argument needed in the original Mecke recursion.
-- source:
--   Pinned Mathlib hasSum_ite_eq and HasSum.unique, real power zero identity.

import Mathlib
open Real
noncomputable section

/-- The constant coefficient of a marked exponential PGF is the zero-argument exponential. -/

theorem AvramDividend.Classical.avram_a27_real_exponential_pgf_series_zero_coefficient_exact_20261117 (C : ℕ → ℝ) (r q : ℝ)
    (hSeries : ∀ z : ℝ, 0 ≤ z → z ≤ 1 →
      HasSum (fun k : ℕ => z ^ k * C k) (Real.exp (q * z - r))) :
    C 0 = Real.exp (-r) := by sorry
