-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_Levy_Dirac_negative2_generator_mark_integral_exact
-- name    : AvramDividend.Classical.avram_jump6_A_original_Levy_Dirac_negative2_generator_mark_integral_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T17:47:21.478949+00:00
-- url     : https://prove2.me/theorems/9ccaaf5a-063a-469a-99d9-79625ccdcf48
-- title:
--   The original Lévy generator integral over its negative Dirac jump measure equals the exact nonlinear ruin-mark value loss
-- statement:
--   For an actual original SpectrallyNegativeLevy model whose negative jump Lévy measure is ν=δ_{−2}, and piecewise quadratic dividend HJB candidate w(z)=0 for z<0 and 1+z+z² otherwise, the original generator term ∫_{(-∞,0)} [w(y+z)−w(y)−w′(y)z 1_{(-1,1)}(z)] ν(dz) equals exactly −(1+y+y²) for reserves 0≤y≤1/5. This is the true nonlinear negative-jump generator drift in the original model, and differs from the defective unit-mark −2 jump source. It directly connects the previously Proved mark-kernel identity 17cbcdef with the physical original Γ generator definition, without replacing or synthesising the Lévy measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_Levy_generator_nonlinear_large_negative2_mark_exact
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_original_Levy_Dirac_negative2_generator_mark_integral_exact
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = Measure.dirac (-2 : ℝ))
    (y : ℝ) (hy : 0 ≤ y) (hcap : y ≤ 1 / 5) :
    (∫ z in Iio (0 : ℝ),
      SpectrallyNegativeLevy.generatorIntegrand
        (fun z : ℝ => if z < 0 then 0 else 1 + z + z ^ 2)
        y z ∂X.ν) = -(1 + y + y ^ 2) := by sorry
