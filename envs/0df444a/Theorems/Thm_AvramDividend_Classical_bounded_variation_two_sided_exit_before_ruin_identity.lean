-- Prove2me | Theorems.Thm_AvramDividend_Classical_bounded_variation_two_sided_exit_before_ruin_identity
-- name    : AvramDividend.Classical.bounded_variation_two_sided_exit_before_ruin_identity
-- status  : Open
-- author  : @WillR
-- created : 2026-10-23T07:13:10.503746+00:00
-- url     : https://prove2.me/theorems/494dbcd1-770a-49c0-986b-046103fab9c4
-- title:
--   Two-sided exit identity before ruin for the bounded-variation branch
-- statement:
--   For a spectrally negative Levy process satisfying the target's Standing assumptions, in the bounded-variation case the discounted probability of exiting upward from the interval before strict ruin equals the ratio of the q-scale function at the initial reserve and at the upper barrier. This is the bounded-variation branch of the exact two-sided exit identity needed by the parent target; it complements the separately stated unbounded-variation stopped-scale identity.
-- source:
--   Source basis: the exact target statement two_sided_exit_before_ruin_identity (5bcf90e1-211c-42db-beac-d92aeb95b5c9), the complete pinned IsScaleFunction definition, and the bounded-variation complement to the Open unbounded-variation stopped q-scale identity (aed50a34-200b-4736-a369-5ae8473e3258). Mathematical purpose: close the BV branch that Standing does not exclude, so the parent can split on X.BoundedVariation and use the unbounded-variation stopped identity on the other branch. This child states a genuine stochastic regime, not a syntactic refactoring.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bounded_variation_two_sided_exit_before_ruin_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    twoSidedExitExpectation X q a x = ENNReal.ofReal (W x / W a) := by sorry
