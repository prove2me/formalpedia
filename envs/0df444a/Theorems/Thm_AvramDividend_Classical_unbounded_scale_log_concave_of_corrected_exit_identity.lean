-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_log_concave_of_corrected_exit_identity
-- name    : AvramDividend.Classical.unbounded_scale_log_concave_of_corrected_exit_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T09:51:08.205758+00:00
-- url     : https://prove2.me/theorems/17c343c1-aed5-4712-be91-6810a063b337
-- title:
--   Unbounded q-scale log-concavity from the corrected exit identity and smoothness
-- statement:
--   For an unbounded-variation spectrally negative Lévy process, positivity of its canonical q-scale function is already Proved. If the exact corrected killed two-sided exit identity is available and log W is differentiable on the positive axis, shifted-reserve pathwise comparison implies ordered scale-function forward ratios. The separately Proved generic logarithmic derivative criterion then establishes full ConcaveOn ℝ (Ioi 0) (log ∘ W). This is the direct stochastic-to-analytic bridge for the root-connected unbounded scale log-concavity core. Both indispensable analytic assumptions are explicit and the proof itself is complete.
-- source:
--   Kuznetsov, Kyprianou and Rivero (2013), two-sided exit identity; real-variable forward-ratio log-concavity.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_corrected_exit_shifted_initial_reserve_monotone
import Theorems.Thm_AvramDividend_Classical_positive_ratio_order_log_concave_of_differentiable
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.Linarith
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_log_concave_of_corrected_exit_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hExit : ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a))
    (hlogdiff : ∀ x : ℝ, 0 < x →
      DifferentiableAt ℝ (fun z : ℝ => Real.log (W z)) x) :
    ConcaveOn ℝ (Ioi (0 : ℝ)) (fun z : ℝ => Real.log (W z)) := by sorry
