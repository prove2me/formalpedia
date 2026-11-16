-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_discounted_Stieltjes_lintegral_lower_mass
-- name    : AvramDividend.Classical.avram_bvb_obstruction_discounted_Stieltjes_lintegral_lower_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:29:29.466307+00:00
-- url     : https://prove2.me/theorems/548e1bc2-11cc-45ac-a43c-448f2774398e
-- title:
--   Exact discounted real Stieltjes cash is bounded below by endpoint discount times interval mass
-- statement:
--   For any nonnegative measure μ on real time, discounted cash on (0,T] is at least the terminal discount factor exp(−T) times the mass of that interval. This is the direct source-independent lintegral lower bound needed for the original zero-barrier dividend cash contradiction, avoiding a full Stieltjes-to-Lebesgue measure equality.
-- source:
--   On (0,T], exp(−t)≥exp(−T). Apply almost-everywhere monotonicity of the Lebesgue lintegral over μ restricted to the interval, and evaluate the constant lintegral as the interval measure times its constant value.

import Mathlib
open MeasureTheory Set Real
open scoped ENNReal

theorem AvramDividend.Classical.avram_bvb_obstruction_discounted_Stieltjes_lintegral_lower_mass (μ : Measure ℝ) (T : ℝ) :
    ENNReal.ofReal (Real.exp (-T)) * μ (Ioc (0 : ℝ) T) ≤
      ∫⁻ t in Ioc (0 : ℝ) T,
        ENNReal.ofReal (Real.exp (-t)) ∂μ := by sorry
