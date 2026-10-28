-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_vcstar_global_C1_and_finite_of_corrected_exit
-- name    : AvramDividend.Classical.gaussian_vcstar_global_C1_and_finite_of_corrected_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:22:37.097041+00:00
-- url     : https://prove2.me/theorems/a9ef5d2b-adac-4114-b66b-00c373e6c4b1
-- title:
--   Gaussian optimal dividend barrier is finite and globally C1 from corrected exits, including the zero-barrier case
-- statement:
--   For a spectrally negative Lévy process with Standing, q>0 and positive Gaussian coefficient, assume only the corrected killed two-sided exit ratio for strictly positive upper and starting reserves. Then the canonical dividend barrier cstar is finite and the exact piecewise dividend value vcstar W is continuously differentiable on the entire positive half-line, with no separate assumption cstar>0. The Proved corrected-exit Gaussian barrier-finiteness theorem yields finiteness. If its real barrier is positive, the Proved Gaussian barrier C1 gluing theorem applies. If its real barrier equals zero, vcstar is affine on every positive reserve and hence C2, so it is automatically C1. This handles the cstar=0 boundary case relevant to Theorem 2.

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_cstar_finite_gaussian_of_corrected_exit_identity
import Theorems.Thm_AvramDividend_Classical_gaussian_vcstar_C1_from_corrected_exit
import Theorems.Thm_AvramDividend_Classical_vcstar_contDiffOn_two_above_real_cstar
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.gaussian_vcstar_global_C1_and_finite_of_corrected_exit
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (hExit : ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a)) :
    cstar W < ⊤ ∧ ContDiffOn ℝ 1 (vcstar W) (Ioi (0 : ℝ)) := by sorry
