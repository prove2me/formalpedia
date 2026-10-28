-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_esscher_tilt_global_monotone_of_corrected_exit
-- name    : AvramDividend.Classical.unbounded_esscher_tilt_global_monotone_of_corrected_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T18:02:34.934116+00:00
-- url     : https://prove2.me/theorems/3c791556-302c-4429-a2c1-d08f3bc69ee1
-- title:
--   Global Esscher-scale monotonicity across the zero boundary from corrected exits
-- statement:
--   The unbounded-variation q-scale function vanishes for negative reserves and at the origin, and its Esscher tilt is nonnegative everywhere. The corrected two-sided exit identity gives monotonicity on positive reserves. Combining these proves that the Esscher-tilted scale is nondecreasing on the entire real line. This is a reusable prerequisite for constructing a Stieltjes measure whose cumulative distribution matches the tilt, needed by the open root-connected cumulative Laplace representation target.
-- source:
--   Avram Palmowski Pistorius (2007), corrected exit formula; Proved scale zero-origin and tilted monotonicity lemmas.

import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_zero_origin_nonnegative_discount
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_tilted_scale_monotone_uniform_bound_of_corrected_exit
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_esscher_tilt_global_monotone_of_corrected_exit
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hExit : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a)) :
    Monotone (fun x : ℝ => Real.exp (-(φ * x)) * W x) := by sorry
