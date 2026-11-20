-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_truegrid_at_zero_clock_is_initial_singleton
-- name    : AvramDividend.Classical.avram_pj_workerC_truegrid_at_zero_clock_is_initial_singleton
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:25:51.720699+00:00
-- url     : https://prove2.me/theorems/5b1382e2-5300-4617-b538-be8a87e7a67a
-- title:
--   True original clipped grid contains initial zero point even when stopping clock equals zero
-- statement:
--   The exact same physical grid used in the original pure-jump Ito source is singleton {0}, not empty, when rho=0. Therefore the payment correction has a zero-time right dividend and requires explicit zero-clock handling.
-- source:
--   Direct audit of potentially false global L1 source 1f802c9c; initial right dividend survives the current filter t=0 or t<rho.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open scoped NNReal ENNReal
open MeasureTheory Set AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_truegrid_at_zero_clock_is_initial_singleton
    {Ω : Type*} (n k : ℕ) (ρ : Ω → ℝ≥0)
    (ω : Ω) (hzero : ρ ω = 0) :
    (((Finset.range (k + 1)).image
      (fun i : ℕ => min
        ((i : ℝ≥0) * ((n : ℝ≥0) / ((k + 1 : ℕ) : ℝ≥0)))
        (ρ ω))).filter (fun t : ℝ≥0 => t = 0 ∨ t < ρ ω))
      = ({0} : Finset ℝ≥0) := by sorry
