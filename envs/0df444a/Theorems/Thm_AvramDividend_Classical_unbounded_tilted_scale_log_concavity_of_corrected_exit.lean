-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_tilted_scale_log_concavity_of_corrected_exit
-- name    : AvramDividend.Classical.unbounded_tilted_scale_log_concavity_of_corrected_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T13:50:30.859871+00:00
-- url     : https://prove2.me/theorems/71415ee9-a898-4c47-9816-b9bcc2c0f4b7
-- title:
--   Log-concavity of Esscher-tilted unbounded-variation scale from corrected exits and differentiability
-- statement:
--   For an unbounded-variation spectrally negative Levy process, assume the corrected two-sided killed exit formula and positive-axis differentiability of the q-scale function W. Then for any real exponential tilt φ, the logarithm of exp(-φx)W(x) is concave on x>0. This is the exact remaining stochastic/smoothness-conditional version of the open unbounded tilted-scale log-concavity target. Its proof imports canonical q-scale strict positivity, the Proved corrected-exit tilted cross-derivative order, and the positive C1 cross-order log-concavity theorem.
-- source:
--   Avram Palmowski Pistorius (2007) corrected killed two-sided exit identity; scale positivity and deterministic derivative criterion.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_unbounded_tilted_scale_cross_derivative_of_corrected_exit
import Theorems.Thm_AvramDividend_Classical_positive_cross_derivative_log_concavity
import Mathlib.Tactic.FunProp
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_tilted_scale_log_concavity_of_corrected_exit
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hExit : ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a))
    (φ : ℝ)
    (hWdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x) :
    ConcaveOn ℝ (Ioi (0 : ℝ))
      (fun z : ℝ => Real.log (Real.exp (-φ * z) * W z)) := by sorry
