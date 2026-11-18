-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_real_exponential_pgf_hasSum_unique_power_series_coefficients_20261117
-- name    : AvramDividend.Classical.avram_a27_real_exponential_pgf_hasSum_unique_power_series_coefficients_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T18:59:06.220095+00:00
-- url     : https://prove2.me/theorems/6310b6a0-9d7b-4ef5-b39c-60deb98b5cc8
-- title:
--   Real power-series uniqueness determines every coefficient from its exponential sum on a nontrivial interval
-- statement:
--   If a real coefficient sequence C has sum sum z^k C_k=exp(qz-r) for every z from zero to one, then each coefficient equals exp(-r)q^k/k!. This is an analytic uniqueness statement requiring an interval identity and local power-series uniqueness; no stochastic or alternative probability-space assumptions.
-- source:
--   Pinned Mathlib analytic uniqueness of real convergent power series and explicit exponential factorial coefficient series.

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a27_real_exponential_pgf_hasSum_unique_power_series_coefficients_20261117
    (C : ℕ → ℝ) (r q : ℝ)
    (hSeries : ∀ z : ℝ, 0 ≤ z → z ≤ 1 →
      HasSum (fun k : ℕ => z ^ k * C k) (Real.exp (q * z - r))) :
    ∀ k : ℕ, C k = Real.exp (-r) * q ^ k / (k.factorial : ℝ) := by sorry
