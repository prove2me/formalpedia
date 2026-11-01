-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_scale_primitive_zero_nonpositive
-- name    : AvramDividend.Classical.avram_wave4_p2_scale_primitive_zero_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:24:45.562039+00:00
-- url     : https://prove2.me/theorems/6dcc8ffe-12b0-4511-9f5f-a722e11d18bb
-- title:
--   Integrated source scale has zero support on nonpositive reserves
-- statement:
--   For any genuine source q-scale W, its oriented integral primitive U(x)=integral from zero to x W is identically zero for x<=0, even in the bounded-variation case when W(0) may be positive. The apparent endpoint atom is a Lebesgue-null singleton, not an integral contribution. This support theorem permits the true compensated generator increment of U on jumps x+y<=0 to be replaced by -U(x)-y W(x), validating the subsequent quadratic crossing strip bound and Fubini calculation.
-- source:
--   Avram, Palmowski and Pistorius (2007), q-scale support and killed-generator boundary crossing. Independent exact zero-support analytic obligation for the primitive route to e8fbc763.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p2_scale_primitive_zero_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : x ≤ 0) :
    (∫ t in (0 : ℝ)..x, W t) = 0 := by sorry
