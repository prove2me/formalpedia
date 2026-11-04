-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_real_void_semigroup_exp_limit
-- name    : AvramDividend.Classical.avram_wave7_06_real_void_semigroup_exp_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:54:03.70537+00:00
-- url     : https://prove2.me/theorems/54ce57a6-4300-46a2-9ed2-d799b80508bd
-- title:
--   Original jump-void semigroup exponential identification from small-time intensity slope
-- statement:
--   An exact analytic bridge for the original marked-jump void semigroup. If p(T)=p(T/n)^n and n(1-p(T/n)) tends to T times the rate, then p(T)=exp(-T times the rate). Requires neither an auxiliary Poisson space nor extra regularity assumptions. W7-06 will instantiate p as the probability of zero original negative-band jumps.
-- source:
--   Exact pinned Mathlib Real.tendsto_one_add_pow_exp_of_tendsto; proof is an analytic bridge to original source.

import Mathlib
open Filter Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_wave7_06_real_void_semigroup_exp_limit
    (p : ℝ≥0 → ℝ) (T : ℝ≥0) (rate : ℝ)
    (hPower : ∀ n : ℕ, 0 < n → p T = (p (T / (n : ℝ≥0))) ^ n)
    (hSlope : Filter.Tendsto
      (fun n : ℕ => (n : ℝ) * (1 - p (T / (n : ℝ≥0))))
      Filter.atTop (nhds ((T : ℝ) * rate))) :
    p T = Real.exp (-((T : ℝ) * rate)) := by sorry
