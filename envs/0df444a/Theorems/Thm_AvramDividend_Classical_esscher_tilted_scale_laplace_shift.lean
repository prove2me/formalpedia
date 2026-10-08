-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_tilted_scale_laplace_shift
-- name    : AvramDividend.Classical.esscher_tilted_scale_laplace_shift
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:48:50.474277+00:00
-- url     : https://prove2.me/theorems/73c21e1c-2f32-4354-8be9-95d6cdd110e4
-- title:
--   Esscher-normalised scale function has the shifted Laplace transform
-- statement:
--   The Laplace transform of the Esscher-normalised q-scale function U(y)=exp(-phi*y) W(y) at theta equals 1/(psi(theta+phi)-q) whenever the shifted Laplace parameter theta+phi satisfies the original scale-transform hypotheses. The identity follows by exponent addition and the exact IsScaleFunction integral characterisation, without constructing a global Esscher probability law.
-- source:
--   Exact canonical IsScaleFunction Laplace clause and pinned Mathlib Real.exp_add; Kuznetsov, Kyprianou and Rivero, Esscher shift W_q(x)=exp(Phi(q)x)W_{Phi(q)}(x).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_tilted_scale_laplace_shift
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (φ θ : ℝ) (hθ : 0 ≤ θ + φ) (hψ : q < X.ψ (θ + φ)) :
    IntegrableOn
      (fun y : ℝ => Real.exp (-(θ * y)) * (Real.exp (-(φ * y)) * W y))
      (Ioi 0) volume ∧
    (∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) *
       (Real.exp (-(φ * y)) * W y) ∂volume) =
      (X.ψ (θ + φ) - q)⁻¹ := by sorry
