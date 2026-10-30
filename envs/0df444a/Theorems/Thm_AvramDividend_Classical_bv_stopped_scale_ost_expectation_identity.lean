-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_stopped_scale_ost_expectation_identity
-- name    : AvramDividend.Classical.bv_stopped_scale_ost_expectation_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T11:34:57.552746+00:00
-- url     : https://prove2.me/theorems/322217fe-647f-4cde-92dc-5e6488349c3a
-- title:
--   BV stopped-scale optional-stopping expectation identity at the two-sided exit
-- statement:
--   Under Standing, for positive discount q and a scale function W of a bounded-variation spectrally negative Levy process, the discounted two-sided exit expectation scaled by W(a) equals W(x). This is the exact optional-stopping identity for the stopped scale martingale at the two-sided exit time.
-- source:
--   Isolates the single remaining obligation (hOST) of parent AvramDividend.Classical.bv_stopped_scale_ost_payoff_balance (09caed2c): remote CE on candidate 16965 showed the type-mismatched use of the Open stopped-scale martingale where this expectation identity is required. Parent follows from this child plus two Proved bridges already in the parent source: pointwise payoff identification (3a6690c2 chat04_strict_upper_exit_scale_payoff) and payoff factorisation (e1242e81 chat04_strict_stopped_exit_payoff_lintegral_factorisation). The child itself takes no Open theorem premises, only Standing/BV/scale hypotheses and exact parent vocabulary, so the decomposition is acyclic.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.bv_stopped_scale_ost_expectation_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
      ENNReal.ofReal (W x) := by sorry
