-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_two_sided_terminal_payoff_uniform_bound_ws01b
-- name    : AvramDividend.Classical.bv_two_sided_terminal_payoff_uniform_bound_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:05:29.958828+00:00
-- url     : https://prove2.me/theorems/eea01828-dcf6-4cb1-82fd-1e259f24170e
-- title:
--   BV strict two-sided terminal discounted scale payoff is bounded by the upper barrier scale
-- statement:
--   The sum of the discounted q-scale rewards on the disjoint upper-first and lower-first strict two-sided exit events is pointwise at most Wq(a) for standing-free bounded-variation Lévy processes at nonnegative reserves x≤a. Unlike the unbounded-variation bound, the possible positive lower boundary Wq(0) is retained and controlled using monotonicity Wq(0)≤Wq(a). Supplies a domination needed for finite-horizon optional stopping and terminal limiting arguments; does not assume no downward creeping or martingale harmonicity.
-- source:
--   Avram two-sided stopped-scale martingale; canonical Proved boundary partition and upper-first terminal bound on Prove2Me.

import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_two_sided_boundary_partition
import Theorems.Thm_AvramDividend_Classical_chat04_strict_stopped_exit_payoff_pointwise_bound

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_two_sided_terminal_payoff_uniform_bound_ws01b
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 ≤ a) (hx : 0 ≤ x) (hxa : x ≤ a) (ω : Ω) :
    (if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0) + (if twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitDownTime X (-x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω))
      else 0) ≤ ENNReal.ofReal (W a) := by sorry
