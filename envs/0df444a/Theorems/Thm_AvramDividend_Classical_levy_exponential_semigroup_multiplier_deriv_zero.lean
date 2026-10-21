-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_exponential_semigroup_multiplier_deriv_zero
-- name    : AvramDividend.Classical.levy_exponential_semigroup_multiplier_deriv_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T22:02:27.473616+00:00
-- url     : https://prove2.me/theorems/007a1530-aeaf-413f-823a-1713883f1f9c
-- title:
--   Time-zero derivative of the exact Lévy exponential semigroup multiplier
-- statement:
--   For the Lévy exponent ψ(θ) obtained from the exact triplet of the given process, and a deterministic reserve x, the analytic real-time function h↦exp(θx)exp(hψ(θ)) has derivative exp(θx)ψ(θ) at h=0. The proof is elementary calculus by differentiating the linear map h↦hψ, composing Real.exp and multiplying by constant exp(θx). Together with the separately requested exact exponential semigroup eigenfunction identity E[exp(θ(x+X_t))]=exp(θx)exp(tψ(θ)) for θ≥0 and t≥0, this yields the right-hand time derivative for exponential test functions. It does not claim differentiation under a Lévy integral or the general generator on arbitrary C² verification functions.
-- source:
--   Pure pinned Mathlib derivative calculus and recorded laplaceExponent; no Open imports. Remote compiler must verify.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_exponential_semigroup_multiplier_deriv_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ x : ℝ) :
    HasDerivAt
      (fun h : ℝ =>
        Real.exp (θ * x) *
          Real.exp (h * laplaceExponent X.c X.σ X.ν θ))
      (Real.exp (θ * x) * laplaceExponent X.c X.σ X.ν θ)
      0 := by sorry
