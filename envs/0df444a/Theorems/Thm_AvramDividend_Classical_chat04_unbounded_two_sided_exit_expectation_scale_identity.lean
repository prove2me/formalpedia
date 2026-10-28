-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_unbounded_two_sided_exit_expectation_scale_identity
-- name    : AvramDividend.Classical.chat04_unbounded_two_sided_exit_expectation_scale_identity
-- status  : Open
-- author  : @WillR
-- created : 2026-10-26T18:02:37.992079+00:00
-- url     : https://prove2.me/theorems/2dcc8bcc-1425-43d3-8967-d403183852cf
-- title:
--   Unbounded-variation two-sided exit expectation times scale value equals initial scale value
-- statement:
--   Let X be a spectrally negative Levy process of unbounded variation, q > 0, and W its q-scale function. For 0 <= x <= a, the killed discounted two-sided exit expectation (up-exit discount mass at levels a - x above and -x below) multiplied by the upper scale value W(a) equals the initial scale value W(x). This isolates the optional-stopping step of the stopped-scale identity: the full stopped identity follows from it via the strict terminal-payoff factorisation at exact barriers and the vanishing discounted down-exit payoff.
-- source:
--   Isolate the hOST gap of the parent stopped-scale repair: Proved factorisation at exact (a-x,-x) barriers plus Proved vanishing down-leg reduces the parent to this expectation identity. Prove via the unbounded-variation killed payoff martingale with time-0 anchor (killed discounted scale initial value) and optional stopping at the two-sided exit; the zero-start case is Proved, the general-x case needs the UBV martingale/harmonicity bridge.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_unbounded_two_sided_exit_expectation_scale_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
      ENNReal.ofReal (W x) := by sorry
