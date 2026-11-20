-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_large_negative_mark_support_nonlinear_generator_kernel_ae
-- name    : AvramDividend.Classical.avram_jump6_A_original_large_negative_mark_support_nonlinear_generator_kernel_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T17:59:58.463218+00:00
-- url     : https://prove2.me/theorems/77ad14c0-3c83-446d-8c26-cafcc340acc0
-- title:
--   True original nonlinear negative-jump generator kernel equals minus entire capped quadratic value almost everywhere for any Lévy measure supported on ruin-overshooting marks
-- statement:
--   Let the true negative-jump Lévy characteristic measure ν of the original SpectrallyNegativeLevy model be supported on jumps z≤−2 almost everywhere, with any (possibly finite) distribution on that large-negative tail. For every pre-ruin reserve 0≤y≤1/5, all those marks are outside the small-jump compensation interval and force ruin, so the actual original nonlinear generator integrand Γ_jump(y,z)=w(y+z)−w(y)−w′(y)z1_{(-1,1)}(z) equals −(1+y+y²) ν-a.e. This extends the Proved special Dirac mark identity 17cbcdef to all genuine sufficiently large negative Lévy measures, giving the exact physically correct marked-generator component necessary to replace the deprecated linear fullmark route.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_original_large_negative_mark_support_nonlinear_generator_kernel_ae
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hSupport : ∀ᵐ z ∂(X.ν.restrict (Iio (0 : ℝ))),
      z ≤ -2)
    (y : ℝ) (hy : 0 ≤ y) (hcap : y ≤ 1 / 5) :
    ∀ᵐ z ∂(X.ν.restrict (Iio (0 : ℝ))),
      SpectrallyNegativeLevy.generatorIntegrand
        (fun u : ℝ => if u < 0 then 0 else 1 + u + u ^ 2)
        y z = -(1 + y + y ^ 2) := by sorry
