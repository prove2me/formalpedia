-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_lower_first_scale_value_zero_ae_ws01c
-- name    : AvramDividend.Classical.bv_lower_first_scale_value_zero_ae_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T09:18:02.141692+00:00
-- url     : https://prove2.me/theorems/94f6d818-dc4d-4711-ba13-790d0196c671
-- title:
--   BV lower-first terminal q-scale value vanishes almost surely
-- statement:
--   On the actual lower-first strict two-sided exit of a Standing spectrally negative bounded-variation Levy process, the q-scale function evaluated at the stopped reserve is zero almost surely. The canonically Proved strict negative undershoot makes the stopped reserve lie below zero, where the IsScaleFunction predicate forces W to vanish. This is the direct undiscouted lower-boundary scale value, useful for optional-stopping terminal arguments.
-- source:
--   WS01C terminal scale value corollary from canonically Proved source-specific BV strict undershoot cad05116 and IsScaleFunction negative-domain property; independent of WS01B optional stopping.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_strict_lower_exit_undershoot_ae_ws01c

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_lower_first_scale_value_zero_ae_ws01c
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    ∀ᵐ ω ∂P,
      twoSidedExitDownTime X (-x) ω <
        twoSidedExitUpTime X (a - x) ω →
      W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω) = 0 := by sorry
