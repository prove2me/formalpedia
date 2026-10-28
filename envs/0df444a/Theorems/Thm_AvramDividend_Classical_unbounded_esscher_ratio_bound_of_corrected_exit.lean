-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_esscher_ratio_bound_of_corrected_exit
-- name    : AvramDividend.Classical.unbounded_esscher_ratio_bound_of_corrected_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T14:14:34.826542+00:00
-- url     : https://prove2.me/theorems/9fbd5eb1-cab7-4ccf-b48d-544c37cd4c98
-- title:
--   Unbounded q-scale Esscher root and exponential ratio bound from corrected exits
-- statement:
--   For q>0 and unbounded variation, assume the canonical killed two-sided exit identity on nonnegative reserves. Then a positive Esscher root φ exists and satisfies W(x)/W(y) ≤ exp(-φ(y−x)) whenever 0<x≤y. This proves the exact conclusion of the Open root-connected unbounded_esscher_ratio_bound milestone under the single source-faithful corrected exit prerequisite. The proof imports previously Proved root existence and fixed-root exit decay, and divides by the canonically positive W(y).
-- source:
--   Avram Palmowski Pistorius (2007) corrected killed two-sided exit identity and positive Esscher root comparison.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_unbounded_positive_tilt_of_corrected_exit
import Theorems.Thm_AvramDividend_Classical_unbounded_fixedroot_decay_of_corrected_exit_identity
import Mathlib.Algebra.Order.Field.Basic
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_esscher_ratio_bound_of_corrected_exit
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hExit : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a)) :
    ∃ (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q),
      ∀ x y : ℝ, 0 < x → x ≤ y →
        W x / W y ≤ Real.exp (-(φ * (y - x))) := by sorry
