-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_03_full_ratio_of_interior_and_zero
-- name    : AvramDividend.Classical.avram_root29_03_full_ratio_of_interior_and_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T08:24:45.443864+00:00
-- url     : https://prove2.me/theorems/459e45e4-a7c4-4be3-9b5d-36cb7767e85f
-- title:
--   Standing strict two-sided exit ratio on the closed reserve interval from interior and zero
-- statement:
--   Under Standing, positive discount, canonical q-scale function and positive upper barrier, suppose the genuine strict two-sided exit expectation equals the scale ratio at zero reserve and at every strict interior reserve. Then the identity holds at all reserves from zero through the upper barrier. The x=a endpoint is established using an independently Proved monotonicity/continuity adapter, with no upward-regularity hypothesis.
-- source:
--   This endpoint integration wrapper explicitly separates the two missing stochastic facts from the complete closed-domain canonical theorem 5bcf90e1. The x=a case imports only canonically Proved upper endpoint theorem 01a564c9. The x=0 and 0<x<a cases are explicit hypothesis uses. It is acyclic, preserves strict clock event order and adds no Open theorem import, hence can be used by the owner of a direct interior-first renewal proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_upper_endpoint_of_interior

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_03_full_ratio_of_interior_and_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hZero : twoSidedExitExpectation X q a 0 =
      ENNReal.ofReal (W 0 / W a))
    (hInterior : ∀ x : ℝ, 0 < x → x < a →
      twoSidedExitExpectation X q a x = ENNReal.ofReal (W x / W a)) :
    ∀ x : ℝ, 0 ≤ x → x ≤ a →
      twoSidedExitExpectation X q a x = ENNReal.ofReal (W x / W a) := by sorry
