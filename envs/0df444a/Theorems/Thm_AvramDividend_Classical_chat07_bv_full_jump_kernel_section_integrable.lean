-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat07_bv_full_jump_kernel_section_integrable
-- name    : AvramDividend.Classical.chat07_bv_full_jump_kernel_section_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T07:31:08.354482+00:00
-- url     : https://prove2.me/theorems/78e6c348-8b92-4f24-a8e6-b0823b21034e
-- title:
--   Fixed-jump integrability of the unit-truncated generator kernel
-- statement:
--   For any strictly positive downward-jump magnitude, the exponentially weighted negative-jump generator kernel with unit-truncated derivative compensation is integrable over positive reserves. For magnitudes below one, use the already proved compensated fixed-jump integrability. For larger magnitudes, compensation vanishes and integrability follows from the two accepted shifted scale integrability statements. This is the per-jump section-integrability requirement for Fubini.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntegrableOn

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat07_bv_full_jump_kernel_section_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ r : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ) (hr : 0 < r) :
    IntegrableOn (fun x : ℝ => Real.exp (-(θ*x)) *
      (W (x-r) - W x +
        (if r < 1 then r * deriv W x else 0)))
      (Ioi (0 : ℝ)) := by sorry
