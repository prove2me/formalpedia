-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_unbounded_stopped_scale_harmonicity_general_reserve
-- name    : AvramDividend.Classical.chat04_unbounded_stopped_scale_harmonicity_general_reserve
-- status  : Open
-- author  : @WillR
-- created : 2026-10-26T07:47:01.038871+00:00
-- url     : https://prove2.me/theorems/be9dc931-e07f-4a95-8207-11114d0a82ff
-- title:
--   Stopped q-scale harmonicity at general reserve for unbounded-variation processes without standing
-- statement:
--   Let X be spectrally negative Levy of unbounded variation, q>0, W its q-scale function, and x<=a. The stopped discounted scale payoff at the first two-sided exit (upper leg paying W at the exit position, lower leg likewise) has mean W x. This is the general-reserve harmonicity premise: with the Proved factorisation 5b55cf54 and the Proved lower-vanishing b697fb05 (via W 0 = 0, Proved c1b8958a), it yields the unbounded stopped-scale balance aed50a34, hence 09663d0d by BV-case split with Open 2bb529c8, hence 3e1ce2c8 by division.
-- source:
--   Exact twoSidedExitUpTime/twoSidedExitDownTime from Definitions.Def_AvramDividend_Classical_TwoSidedExit and IsScaleFunction from Definitions.Def_AvramDividend_Classical_ScaleFunction; no Standing assumed, matching aed50a34 hypotheses.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_unbounded_stopped_scale_harmonicity_general_reserve
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (hxa : x ≤ a) :
    (∫⁻ ω, (if twoSidedExitUpTime X (a - x) ω <
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
      else 0) ∂P) = ENNReal.ofReal (W x) := by sorry
