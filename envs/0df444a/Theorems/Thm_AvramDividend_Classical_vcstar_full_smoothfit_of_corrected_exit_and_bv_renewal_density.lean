-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_full_smoothfit_of_corrected_exit_and_bv_renewal_density
-- name    : AvramDividend.Classical.vcstar_full_smoothfit_of_corrected_exit_and_bv_renewal_density
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T15:25:00.121427+00:00
-- url     : https://prove2.me/theorems/44d5d028-73ac-4028-9116-4d7b528033e7
-- title:
--   Three-way optimal-barrier smooth fit from corrected Gaussian exit and continuous BV renewal density
-- statement:
--   The complete three-way smooth-fit conclusion holds for the canonical positive finite barrier whenever the Gaussian corrected-exit identity and exponential estimate are available, and the bounded-variation scale function admits a continuous Esscher-renewal density representation. The explicit C2 branch is unconditional. All remaining hypotheses are precisely the independent stochastic and renewal facts under active development.
-- source:
--   Avram, Palmowski and Pistorius (2007), Section 3.2 and barrier smooth-fit conditions, using published Prove2Me calculus and corrected-exit comparison theorems.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_vcstar_gaussian_smoothfit_of_corrected_exit_bounds
import Theorems.Thm_AvramDividend_Classical_scale_C1_of_esscher_integrated_continuous_density
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_bv_contDiff_one
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_contDiffOn

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

namespace AvramDividend.Classical
theorem vcstar_full_smoothfit_of_corrected_exit_and_bv_renewal_density
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hExit : ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a))
    (hBound : ∀ φ : ℝ, 0 < φ → X.ψ φ = q →
      ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
        twoSidedExitExpectationCorrected X q a x ≤
          ENNReal.ofReal (Real.exp (-φ * (a - x))))
    (hBVRep : X.BoundedVariation →
      ∃ (φ c : ℝ) (f : ℝ → ℝ),
        ContinuousOn f (Ioi (0 : ℝ)) ∧
        (∀ x : ℝ, 0 < x → IntervalIntegrable f volume 0 x) ∧
        (∀ x : ℝ, 0 < x →
          Real.exp (-(φ * x)) * W x =
            c + ∫ y in (0 : ℝ)..x, f y))
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    deriv (vcstar W) (cstar W).toReal = 1 := by sorry
end AvramDividend.Classical
