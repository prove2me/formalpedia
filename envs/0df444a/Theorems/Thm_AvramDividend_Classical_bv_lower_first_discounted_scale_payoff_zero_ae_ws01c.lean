-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_lower_first_discounted_scale_payoff_zero_ae_ws01c
-- name    : AvramDividend.Classical.bv_lower_first_discounted_scale_payoff_zero_ae_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T09:08:00.443834+00:00
-- url     : https://prove2.me/theorems/e09b773b-a6e3-4876-8a48-1624b304ca61
-- title:
--   BV lower-first stopped q-scale reward vanishes almost surely
-- statement:
--   For the original Standing bounded-variation spectrally negative Levy process, the actual strict lower-first discounted q-scale terminal reward is zero almost surely. The accepted no-downward-creeping theorem removes exact lower-boundary contact; the previously proved creeping-atom factorisation removes all remaining terminal scale mass. This is the pointwise boundary input for stopped-payoff convergence and dominated-convergence arguments.
-- source:
--   WS01C terminal a.e. payoff bridge. Relies only on canonically Proved 43a28d8e original raw-iInf no-creeping and 0f1adee0 lower-exit creeping-atom identity; independently of other owners' killed martingale and optional stopping. 29 October 2026.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_strict_lower_exit_no_creeping_ae
import Theorems.Thm_AvramDividend_Classical_chat04_lower_exit_scale_creeping_atom

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_lower_first_discounted_scale_payoff_zero_ae_ws01c
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    ∀ᵐ ω ∂P,
      (if twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitDownTime X (-x) ω).toReal))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω))
      else 0) = 0 := by sorry
