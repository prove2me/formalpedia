-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom
-- name    : AvramDividend.Classical.avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:46:04.170168+00:00
-- url     : https://prove2.me/theorems/1fb597ac-8e48-41be-a4e3-03b7681f3915
-- title:
--   Original zero-horizon discounted dividend Stieltjes reward equals the complete time-zero atom
-- statement:
--   For the original dividendMeasure D ω on real time and the canonical paymentTimes σ, at finite horizon T=0 the complete discounted Stieltjes payout is exactly the dividendMeasure mass of the singleton {0}, for every discount rate q and stopping clock σ. This verifies that the initial right dividend atom is retained even at immediate ruin, and that its discount factor is exactly one.
-- source:
--   Direct unfolding of the authoritative paymentTimes definition and the zero-time exponential identity; an exact boundary check for corrected UBV finite-horizon value cc518136, preserving the source Stieltjes measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (σ : ℝ≥0∞) (q : ℝ) :
    (∫⁻ t in paymentTimes σ ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      (dividendMeasure D ω) ({0} : Set ℝ) := by sorry
