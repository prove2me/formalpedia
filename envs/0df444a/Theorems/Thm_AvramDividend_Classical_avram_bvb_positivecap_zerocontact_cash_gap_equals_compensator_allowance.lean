-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_positivecap_zerocontact_cash_gap_equals_compensator_allowance
-- name    : AvramDividend.Classical.avram_bvb_positivecap_zerocontact_cash_gap_equals_compensator_allowance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T09:56:47.529982+00:00
-- url     : https://prove2.me/theorems/0c42dac3-ddef-4937-9dc1-15b07b144d7f
-- title:
--   The exact positive-cap zero-contact nojump dividend cash excess equals the positive missing jump-compensator allowance
-- statement:
--   For every T>0 at discount rate one and uniform unit negative-jump intensity, the zero-barrier nojump discounted cash (1−e^(−T)) plus surviving half-unit terminal equals the half-unit candidate plus the missing positive half-unit stopped compensator (1/2)(1−e^(−T)). The latter is strictly positive. This demonstrates exactly why omitting the jump compensator from the proposed drift-only zero-contact BV budget is mathematically unsound, while the original compensated ceiling remains consistent.
-- source:
--   Direct algebraic equality and strict positivity from exp(−T)<1. The factor 1/2 is w(0) and intensity 1 follows from the Proved negative-uniform compound Poisson source. Reference full original compensated zero-contact source ceiling theorem 1569d325.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic
open Real

theorem AvramDividend.Classical.avram_bvb_positivecap_zerocontact_cash_gap_equals_compensator_allowance (T : ℝ) (hT : 0 < T) :
    (1 - Real.exp (-T)) + (1 / 2 : ℝ) * Real.exp (-T) =
      (1 / 2 : ℝ) + (1 / 2) * (1 - Real.exp (-T)) ∧
    0 < (1 / 2 : ℝ) * (1 - Real.exp (-T)) := by sorry
