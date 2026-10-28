-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_positive_tilt_of_corrected_exit
-- name    : AvramDividend.Classical.unbounded_positive_tilt_of_corrected_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:05:50.62438+00:00
-- url     : https://prove2.me/theorems/4b96094e-9af5-4d1e-97c5-566b8cbbe172
-- title:
--   Unbounded-variation positive and Esscher-monotone scale from corrected two-sided exit
-- statement:
--   For any q>0, any unbounded-variation spectrally negative Lévy process and its canonical q-scale W, the corrected killed upward-before-ruin exit identity implies W(x)>0 for x>0 and the existence of an unconditional positive root φ>0 with ψ(φ)=q such that exp(−φx)W(x) is nondecreasing on positive times. No Standing assumption is needed. The Proved unbounded variation positivity and root existence lemmas supply the first two results; the Proved fixed-root exponential exit comparison and generic decay-to-monotonicity lemma yield the final assertion. Isolates the genuine stochastic exit-identity dependency for the root's tilted monotonicity.

import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_unbounded_fixedroot_decay_of_corrected_exit_identity
import Theorems.Thm_AvramDividend_Classical_exit_decay_implies_tilted_monotone
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_positive_tilt_of_corrected_exit
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hExit : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a)) :
    (∀ x : ℝ, 0 < x → 0 < W x) ∧
      ∃ φ : ℝ, 0 < φ ∧ X.ψ φ = q ∧
        MonotoneOn (fun x : ℝ => Real.exp (-(φ * x)) * W x)
          (Ioi (0 : ℝ)) := by sorry
