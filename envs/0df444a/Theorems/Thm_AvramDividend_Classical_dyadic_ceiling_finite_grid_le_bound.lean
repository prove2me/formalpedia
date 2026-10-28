-- Prove2me | Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_finite_grid_le_bound
-- name    : AvramDividend.Classical.dyadic_ceiling_finite_grid_le_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T21:33:39.31362+00:00
-- url     : https://prove2.me/theorems/16a09ed8-7c62-4dfe-a271-7d9e49781f70
-- title:
--   Every point of a bounded dyadic ceiling grid lies within one unit of the bound
-- statement:
--   For any nonnegative horizon H and dyadic resolution n, every time in the explicit finite grid consisting of k/2^n for k from 0 through ceil(H 2^n) is at most H+1. This uniform bound on all grid points, rather than merely the attained stopping-time values, supplies a single lawful finite Esscher terminal horizon for the dyadic stopped-increment limiting argument.
-- source:
--   Elementary dyadic ceiling bound; reuses the canonically Proved dyadic_ceiling_rounding_bounds (57b560d3-993c-406e-b3e8-bd006ac45674) and Mathlib's ordered real arithmetic. Used in the standard finite-grid proof of the strong Markov property; no Wiener–Hopf or scale-function hypothesis.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_rounding_bounds

open AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.dyadic_ceiling_finite_grid_le_bound
    (H : ℝ≥0) (n : ℕ) :
    ∀ s ∈ (Finset.range (Nat.ceil ((H : ℝ) * (2 : ℝ) ^ n) + 1)).image
      (fun k : ℕ => (k : ℝ≥0) / (2 : ℝ≥0) ^ n), s ≤ H + 1 := by sorry
