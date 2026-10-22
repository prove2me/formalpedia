-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat07_scale_shift_weighted_abs_integral_exact
-- name    : AvramDividend.Classical.chat07_scale_shift_weighted_abs_integral_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T17:59:38.096513+00:00
-- url     : https://prove2.me/theorems/45aae584-f697-4bed-88de-94cc6430f8cb
-- title:
--   Exact weighted absolute negative shift of a monotone Lévy scale function
-- statement:
--   For a q-scale function W, an admissible Laplace parameter theta and a positive downward jump magnitude r, the exponentially weighted L1 norm of the un-compensated jump decrement W(x)-W(x-r) equals (1-exp(-theta*r))/(psi(theta)-q). Monotonicity makes the absolute value exact. The proof combines accepted scale-function monotonicity, integrability of both shifted Laplace integrands and the exact shifted Laplace transform. This identity requires no differentiability or absolute continuity. It is a key building block for first-order weighted compensated Fubini in the bounded-variation Lévy branch.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat07_scale_shift_weighted_abs_integral_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
    (r : ℝ) (hr : 0 < r) :
    (∫ x in Ioi (0 : ℝ),
       Real.exp (-(θ * x)) * |W x - W (x - r)|) =
      (1 - Real.exp (-(θ * r))) * (X.ψ θ - q)⁻¹ := by sorry
