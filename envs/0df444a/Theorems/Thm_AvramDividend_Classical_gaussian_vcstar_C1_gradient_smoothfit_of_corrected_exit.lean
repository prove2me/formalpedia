-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_vcstar_C1_gradient_smoothfit_of_corrected_exit
-- name    : AvramDividend.Classical.gaussian_vcstar_C1_gradient_smoothfit_of_corrected_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:00:55.410268+00:00
-- url     : https://prove2.me/theorems/0e6d6d18-96a1-4a2f-85ec-e6debdd6c193
-- title:
--   Gaussian dividend barrier global C1, derivative HJB bound and smooth fit from corrected exits
-- statement:
--   Under a positive Gaussian coefficient and the exact corrected killed two-sided exit identity, suppose the standing discounted spectrally negative Lévy scale W has finite strictly positive optimal barrier c*. Then the exact piecewise dividend value vcstar W is continuously differentiable at every positive reserve, its gradient satisfies v'(x)≥1 throughout the positive half-line, and its derivative equals one at the canonical optimal barrier. The explicit C1 regularity and positive monotone Esscher tilt follow from existing Proved theorems, and the remaining derivative results use Proved optimal-barrier gradient and corrected-exit smooth-fit lemmas. This is the complete HJB gradient-side certificate conditional only on the outstanding corrected exit identity.

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_gaussian_tilt_monotone_of_corrected_exit_identity
import Theorems.Thm_AvramDividend_Classical_vcstar_C1_of_scale_C1_tilt
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one_of_scale_C1_tilt
import Theorems.Thm_AvramDividend_Classical_vcstar_gaussian_smoothfit_of_corrected_exit_identity
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.gaussian_vcstar_C1_gradient_smoothfit_of_corrected_exit
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hσ : 0 < X.σ)
    (hExit : ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a)) :
    ContDiffOn ℝ 1 (vcstar W) (Ioi (0 : ℝ)) ∧
    (∀ x : ℝ, 0 < x →
      DifferentiableAt ℝ (vcstar W) x ∧
        1 ≤ deriv (vcstar W) x) ∧
    deriv (vcstar W) (cstar W).toReal = 1 := by sorry
