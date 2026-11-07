-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f18_discounted_finite_clock_split_le
-- name    : AvramDividend.Classical.avram_p4_f18_discounted_finite_clock_split_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T23:23:46.171397+00:00
-- url     : https://prove2.me/theorems/7d747dc1-a783-4ff1-8f27-97be632966d2
-- title:
--   Discounted finite first-passage reward is bounded by early-passage mass plus a late-time exponential tail
-- statement:
--   For any nonnegative discount rate q, positive-time threshold epsilon and extended nonnegative clock t, the stopped exponential reward equals zero at infinity, is at most one when t is early, and at most exp(-q epsilon) when t is late. This deterministic bound enables a nontrivial uniform first-passage probability estimate from the exact Levy strict-upcrossing transform.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f18_discounted_finite_clock_split_le
    (q : ℝ) (hq : 0 ≤ q) (ε : ℝ≥0) (t : ℝ≥0∞) :
    (if t < ⊤ then ENNReal.ofReal
      (Real.exp (-(q * ENNReal.toReal t))) else 0) ≤
    (if t < (ε : ℝ≥0∞) then 1 else
      ENNReal.ofReal (Real.exp (-(q * (ε : ℝ))))) := by sorry
