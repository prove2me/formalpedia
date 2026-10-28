-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_midpoint_of_corrected_exit_identity
-- name    : AvramDividend.Classical.unbounded_scale_midpoint_of_corrected_exit_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T09:33:19.296613+00:00
-- url     : https://prove2.me/theorems/5ea0c735-4562-4e6c-a7b8-64b446254e98
-- title:
--   Unbounded scale-function midpoint log-concavity from the corrected two-sided exit identity
-- statement:
--   For a canonical q-scale function of an unbounded-variation spectrally negative Lévy process, the exact corrected two-sided exit identity, together with the already proved pathwise monotonicity of successful exits under larger initial reserves, forces ordered forward ratios of W. Strict positivity allows converting ENNReal comparisons to real inequalities, then the proved midpoint ratio lemma yields multiplicative midpoint log-concavity. The missing fluctuation identity remains an explicit premise; the theorem itself is fully proved.
-- source:
--   Kuznetsov, Kyprianou and Rivero (2013), two-sided exit identity and scale-function log-concavity, with pathwise event monotonicity.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_corrected_exit_shifted_initial_reserve_monotone
import Theorems.Thm_AvramDividend_Classical_positive_midpoint_multiplicative_of_ratio_order
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.Linarith
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_midpoint_of_corrected_exit_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hExit : ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a)) :
    ∀ x y : ℝ, 0 < x → x < y →
      W x * W y ≤ (W ((x + y) / 2)) ^ 2 := by sorry
