-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_05_signed_neumann_sum_integrable
-- name    : AvramDividend.Classical.avram_wave3_05_signed_neumann_sum_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T23:35:51.401537+00:00
-- url     : https://prove2.me/theorems/9210d3c0-28af-485b-958c-c792c4eae0ec
-- title:
--   Gaussian signed Neumann sum is globally L1 under an integrable positive-power envelope
-- statement:
--   For signed Gaussian causal convolution powers P_n dominated pointwise in absolute value by nonnegative envelope powers F_n, if the signed and envelope powers are integrable, the positive series converges pointwise and its term masses are summable, then the entire signed Neumann density sum is integrable on the positive half-line. This is the analytic bridge from the already constructed Gaussian derivative-resolvent Neumann powers to global weighted second-derivative integrability. It does not assert that the actual scale W second derivative is already identified with that sum.
-- source:
--   Avram-Palmowski-Pistorius 2007 Lemma 4, Gaussian Volterra route; Proved causal_neumann_C1_with_power_domination 4322e6f7 and nonnegative_integrable_tsum_of_summable_integrals 2df366d2.

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Theorems.Thm_AvramDividend_Classical_nonnegative_integrable_tsum_of_summable_integrals

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.avram_wave3_05_signed_neumann_sum_integrable
    (P F : ℕ → ℝ → ℝ)
    (hPL1 : ∀ n : ℕ, IntegrableOn (P n) (Ioi (0 : ℝ)) volume)
    (hFL1 : ∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume)
    (hFpos : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ F n x)
    (hDom : ∀ n : ℕ, ∀ x : ℝ, |P n x| ≤ F n x)
    (hFpoint : ∀ x : ℝ, Summable (fun n : ℕ => F n x))
    (hFmass : Summable (fun n : ℕ =>
      ∫ x in Ioi (0 : ℝ), F n x ∂volume)) :
    IntegrableOn (fun x : ℝ => ∑' n : ℕ, P n x)
      (Ioi (0 : ℝ)) volume := by sorry
