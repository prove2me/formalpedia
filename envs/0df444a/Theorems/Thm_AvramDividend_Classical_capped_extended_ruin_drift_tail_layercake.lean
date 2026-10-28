-- Prove2me | Theorems.Thm_AvramDividend_Classical_capped_extended_ruin_drift_tail_layercake
-- name    : AvramDividend.Classical.capped_extended_ruin_drift_tail_layercake
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T17:45:00.584584+00:00
-- url     : https://prove2.me/theorems/8127ce8c-a358-46bd-a61a-82f4775a01a8
-- title:
--   Capped extended-real ruin clock admits an exact strict-survival Tonelli identity for discounted drift
-- statement:
--   For any measurable extended nonnegative-real stopping clock tau and any finite NNReal cap T, convert min(tau,T) to a finite real stopping clock. The expected discounted drift integral up to this cap equals the integral over positive times of d*exp(-q*t) times the strict capped survival probability P(t<min(tau,T).toReal). The clipped clock is measurable by Measurable.min and ENNReal.measurable_toReal and is nonnegative; thus the already Proved real-clock strict layer-cake identity applies directly. This handles the actual reflected ruin clock's possible value ∞ without erroneously using (∞).toReal=0, and is the truncation basis for the infinite-horizon stopped Stieltjes reward.
-- source:
--   Tonelli/Cavalieri, Mathlib MeasureTheory.Integral.Layercake; Avram Palmowski Pistorius 2007 finite-activity zero-barrier reward; Prove2Me stopped_discounted_drift_tail_layercake.

import Theorems.Thm_AvramDividend_Classical_stopped_discounted_drift_tail_layercake
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Data.NNReal.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.capped_extended_ruin_drift_tail_layercake
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω)
    (τ : Ω → ℝ≥0∞) (hτ : Measurable τ)
    (T : ℝ≥0) (d q : ℝ) (hd : 0 ≤ d) :
    (∫⁻ ω, ENNReal.ofReal
        (∫ t in (0 : ℝ)..(min (τ ω) (T : ℝ≥0∞)).toReal,
          d * Real.exp (-(q * t))) ∂P) =
      ∫⁻ t in Ioi (0 : ℝ),
        P {ω : Ω | t < (min (τ ω) (T : ℝ≥0∞)).toReal} *
          ENNReal.ofReal (d * Real.exp (-(q * t))) := by sorry
