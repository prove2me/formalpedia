-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_comp16_diagonal_vanishing_error_of_fixed_band_rates
-- name    : AvramDividend.Classical.avram_p3_comp16_diagonal_vanishing_error_of_fixed_band_rates
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T21:48:43.93125+00:00
-- url     : https://prove2.me/theorems/c492dfa1-9c48-49af-99ae-d74f0af1cf94
-- title:
--   Diagonal physical-grid errors vanish when each fixed-band rate has an eventual certified bound
-- statement:
--   For an arbitrary fixed-band error family Err(k,n), if the rate after threshold N(k) is bounded by ε(k) for each positive k and ε(k) tends to zero, a cofinal diagonal schedule κ(n) exists with N(κ(n))≤n and Err(κ(n),n)→0. The index 0 is a dummy early stage and needs no bound.
-- source:
--   Direct application of Avram P3-COMP16 safe diagonal schedule plus `squeeze_zero_norm`, under explicit fixed-band error bound. This theorem does not claim the Lévy source estimate itself, whose verification remains needed for the original strict-cash bridge.

import Mathlib
open Filter
noncomputable section

theorem AvramDividend.Classical.avram_p3_comp16_diagonal_vanishing_error_of_fixed_band_rates
    (N : ℕ → ℕ) (hN0 : N 0 = 0)
    (hNge : ∀ k, k ≤ N k)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (nhds 0))
    (Err : ℕ → ℕ → ℝ)
    (hErr : ∀ k n, 0 < k → N k ≤ n → |Err k n| ≤ |ε k|) :
    ∃ κ : ℕ → ℕ,
      (∀ n, κ n ≤ n) ∧
      (∀ n, N (κ n) ≤ n) ∧
      Tendsto κ atTop atTop ∧
      Tendsto (fun n => Err (κ n) n) atTop (nhds 0) := by sorry
