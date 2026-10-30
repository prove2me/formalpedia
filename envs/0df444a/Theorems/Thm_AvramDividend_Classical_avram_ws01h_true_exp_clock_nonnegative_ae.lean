-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_true_exp_clock_nonnegative_ae
-- name    : AvramDividend.Classical.avram_ws01h_true_exp_clock_nonnegative_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T15:53:26.079106+00:00
-- url     : https://prove2.me/theorems/59996899-e332-4b36-b4ac-b10c50af2387
-- title:
--   Genuine real Exp(p) observation clock is nonnegative almost everywhere
-- statement:
--   Under the actual real exponential clock of rate p>0, almost every observed real time is nonnegative. From the canonically proved genuine strict upper-tail law at zero, the positive half-line has probability one. Under the probability expMeasure, its complement Iic 0 has mass zero; the negative half-line is a subset. This removes the redundant clock positivity test when identifying the Qp rational path-space reward in the genuine source killed first-record renewal; no fictitious positive-clock probability measure is assumed.
-- source:
--   Proved avram_ws01e_b_expMeasure_strict_survival_real, Mathlib prob_compl_eq_one_sub, ae_iff, measure_mono_null.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_expMeasure_strict_survival_real

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_ws01h_true_exp_clock_nonnegative_ae
    (p : ℝ) (hp : 0 < p) :
    ∀ᵐ r : ℝ ∂(expMeasure p), 0 ≤ r := by sorry
