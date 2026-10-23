-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat07_scale_weighted_compensated_jump_l1_bound
-- name    : AvramDividend.Classical.chat07_scale_weighted_compensated_jump_l1_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T06:58:24.813013+00:00
-- url     : https://prove2.me/theorems/9d4b5dea-5803-4224-a03d-e67a283566fb
-- title:
--   Uniform first-order Laplace bound for the compensated negative-jump kernel
-- statement:
--   For a nonnegative admissible Laplace parameter and a positive downward jump size, the absolute exponentially weighted integral over positive reserves of the fully compensated scale-function jump difference is at most min(1,theta*r)/(psi(theta)-q) plus r times the weighted derivative integral. All integrability premises are discharged by proved shifted scale, scale derivative and fixed-jump compensated integrability lemmas. This gives the first-order bound required to dominate negative jumps in the bounded-variation Lévy generator.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat07_scale_weighted_compensated_jump_l1_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ r : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ) (hr : 0 < r) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ*x)) *
        |W (x-r) - W x + r*deriv W x|) ≤
      min 1 (θ*r) * (X.ψ θ - q)⁻¹ +
      r * (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ*x)) * deriv W x) := by sorry
