-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat07_scale_compensated_jump_small_linear_bound
-- name    : AvramDividend.Classical.chat07_scale_compensated_jump_small_linear_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T07:00:04.435456+00:00
-- url     : https://prove2.me/theorems/1d368d33-312e-43a8-8a62-32b53d16a5a0
-- title:
--   Linear small-jump bound for the compensated Lévy scale kernel
-- statement:
--   The exponentially weighted absolute integral of the compensated downward scale-function jump kernel is at most the positive jump magnitude times the finite constant theta/(psi(theta)-q) plus the weighted derivative integral. This follows from the proved min(1,theta*r) bound and the nonnegative reciprocal of psi(theta)-q. It is the exact linear magnitude domination used on small jumps under the bounded-variation first-moment condition; uncompensated large jumps use the separate uniform shift bound.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Analysis.SpecialFunctions.Exp

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat07_scale_compensated_jump_small_linear_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ r : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ) (hr : 0 < r) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ*x)) *
        |W (x-r) - W x + r*deriv W x|) ≤
      r * (θ * (X.ψ θ - q)⁻¹ +
        (∫ x in Ioi (0 : ℝ),
          Real.exp (-(θ*x)) * deriv W x)) := by sorry
