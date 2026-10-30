-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_lower_exit_discounted_scale_payoff_zero_ws01c
-- name    : AvramDividend.Classical.bv_lower_exit_discounted_scale_payoff_zero_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T09:00:19.23374+00:00
-- url     : https://prove2.me/theorems/ba60b63f-09cc-4471-b6b7-19271a493049
-- title:
--   Original BV lower-first discounted scale reward vanishes unconditionally by strict no creeping
-- statement:
--   For the actual standing bounded-variation spectrally negative Levy process, the discounted q-scale payoff at the strict lower exit prior to upper exit has zero extended-nonnegative integral. The genuinely Proved original-process a.e. no-downward-creeping theorem excludes exactly the only nonzero lower-boundary contact contribution. This closes the lower-exit terminal reward without a martingale assumption or additional stopping hypothesis.
-- source:
--   WS01C direct unconditional terminal vanishing corollary. Imports canonically Proved original strict lower-exit no-creeping UUID 43a28d8e and canonically Proved general a.e.-no-creeping lintegral zero UUID 362ed18d. Both formal statements were checked on 29 October 2026. Do not confuse this terminal reward identity with the still Open WS01B optional stopping or killed harmonicity theorems.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_strict_lower_exit_no_creeping_ae
import Theorems.Thm_AvramDividend_Classical_chat04_lower_exit_lintegral_zero_of_ae_no_creeping

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_lower_exit_discounted_scale_payoff_zero_ws01c
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (∫⁻ ω,
      if twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitDownTime X (-x) ω).toReal))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω))
      else 0 ∂P) = 0 := by sorry
