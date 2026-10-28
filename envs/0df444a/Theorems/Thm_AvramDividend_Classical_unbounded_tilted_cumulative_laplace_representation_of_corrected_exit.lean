-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_tilted_cumulative_laplace_representation_of_corrected_exit
-- name    : AvramDividend.Classical.unbounded_tilted_cumulative_laplace_representation_of_corrected_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T18:21:37.961181+00:00
-- url     : https://prove2.me/theorems/21a19c48-8ea9-4698-b0c1-f9e20d89aaf9
-- title:
--   Unbounded Esscher cumulative Laplace representation from corrected exit identity
-- statement:
--   Assuming the corrected two-sided exit identity and unbounded variation, the Esscher-normalised q-scale function is continuous and nondecreasing. Construct its Stieltjes cumulative measure, prove the cumulative distribution is finite and strictly positive for positive reserves, and show the exponential-weighted Laplace integrals agree and are integrable above a finite abscissa.
-- source:
--   Avram, Palmowski and Pistorius (2007), unbounded-variation Esscher transform and Stieltjes representation, conditional on the corrected exit identity.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_zero_origin_nonnegative_discount
import Theorems.Thm_AvramDividend_Classical_scaleFunction_global_continuous_of_zero_origin
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_tilt_global_monotone_of_corrected_exit
import Theorems.Thm_AvramDividend_Classical_continuous_monotone_real_has_stieltjes_cumulative_measure
import Theorems.Thm_AvramDividend_Classical_chat04_psi_eventually_gt_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_tilted_cumulative_laplace_representation_of_corrected_exit
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hExit : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a)) :
    ∃ (β : Measure ℝ) (φ b : ℝ),
      0 < φ ∧
      (∀ x : ℝ, β (Iic x) ≠ ⊤) ∧
      (∀ x : ℝ, 0 < x → 0 < β (Iic x)) ∧
      ∀ θ : ℝ, b < θ →
        IntegrableOn (fun x : ℝ => Real.exp (-θ * x) *
          (Real.exp (-φ * x) * W x)) (Ioi 0) ∧
        IntegrableOn (fun x : ℝ => Real.exp (-θ * x) *
          (β (Iic x)).toReal) (Ioi 0) ∧
        ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) *
          (Real.exp (-φ * x) * W x) =
          ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) *
            (β (Iic x)).toReal := by sorry
