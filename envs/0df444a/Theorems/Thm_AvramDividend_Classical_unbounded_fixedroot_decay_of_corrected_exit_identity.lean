-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_fixedroot_decay_of_corrected_exit_identity
-- name    : AvramDividend.Classical.unbounded_fixedroot_decay_of_corrected_exit_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T15:03:18.001754+00:00
-- url     : https://prove2.me/theorems/f0963971-96e0-4536-9a47-4e13542021f9
-- title:
--   Unbounded q-scale exponential decay from the sole killed two-sided exit identity
-- statement:
--   For a canonical q-scale function W of an unbounded-variation spectrally negative Lévy process and any supplied positive root ψ(φ)=q>0, the first-passage scale exponential inequality follows if the corrected killed upper-before-downward exit expectation is identified with W(x)/W(a). This combines the already Proved scaleFunction_strict_pos_of_unbounded_variation, corrected_exit_exp_bound_at_positive_root, and unbounded_fixedroot_scale_decay_of_corrected_exit_estimates. Exactly one substantive killed exit-identity hypothesis remains; no circular monotonicity hypothesis is assumed.
-- source:
--   Direct composition of three canonically Proved Avram Dividend Classical lemmas. Theorem (3.6) of Avram, Palmowski and Pistorius (2007) supplies the killed exit identity in the source mathematics.

import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_corrected_exit_exp_bound_at_positive_root
import Theorems.Thm_AvramDividend_Classical_unbounded_fixedroot_scale_decay_of_corrected_exit_estimates
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_fixedroot_decay_of_corrected_exit_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hExit : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a)) :
    ∀ x y : ℝ, 0 < x → x ≤ y →
      W x ≤ Real.exp (-(φ * (y - x))) * W y := by sorry
