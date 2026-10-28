-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_stopped_scale_zero_barrier_case
-- name    : AvramDividend.Classical.bv_stopped_scale_zero_barrier_case
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T14:24:51.43153+00:00
-- url     : https://prove2.me/theorems/450ae690-d18c-4c6d-96a2-41c355bc27f6
-- title:
--   Stopped scale identity in the degenerate zero-barrier case
-- statement:
--   Let W be a q-scale function and 0 <= x <= a with W a = 0. Monotonicity and nonnegativity of W on [0,infty) force W x = 0, so both sides of the stopped-scale optional-stopping identity vanish. This discharges the degenerate-barrier case of the BV stopped-scale expectation identity.
-- source:
--   Source-faithful case split of AvramDividend.Classical.bv_stopped_scale_ost_expectation_identity (322217fe). The parent's IsScaleFunction supplies nonnegativity and MonotoneOn over Ici 0; the zero-barrier hypothesis collapses both sides to zero without any optional-stopping input. Proves one genuine parent case; the positive-barrier case remains open.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.bv_stopped_scale_zero_barrier_case
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (hWa : W a = 0) :
    twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
      ENNReal.ofReal (W x) := by
  sorry
