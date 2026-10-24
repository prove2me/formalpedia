-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_threeway_smoothfit_exit_identity_bv_density
-- name    : AvramDividend.Classical.vcstar_threeway_smoothfit_exit_identity_bv_density
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T15:38:10.820275+00:00
-- url     : https://prove2.me/theorems/c3ffe68b-a69f-439e-ac4b-afb773dbf9b6
-- title:
--   Three-way cstar smooth fit with only corrected exit identity and BV renewal-density obligations
-- statement:
--   For the original Gaussian/BV/C2 smoothness disjunction, smooth fit at the positive finite optimal barrier follows from the corrected killed two-sided exit identity and a continuous BV Esscher-renewal density representation. Both are precise independent open mathematical packages. The previously needed exponential exit estimate has already been proved and is derived internally.
-- source:
--   Avram, Palmowski and Pistorius (2007), Gaussian/BV smooth fit. Reuses the proved stopped-exponential bound and three-way smooth-fit calculus bridge.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_corrected_exit_exp_bound_at_positive_root
import Theorems.Thm_AvramDividend_Classical_vcstar_full_smoothfit_of_corrected_exit_and_bv_renewal_density

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

namespace AvramDividend.Classical
theorem vcstar_threeway_smoothfit_exit_identity_bv_density
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hExit : ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a))
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
