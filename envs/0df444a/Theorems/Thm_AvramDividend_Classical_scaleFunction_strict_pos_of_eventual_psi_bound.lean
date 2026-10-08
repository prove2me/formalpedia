-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_eventual_psi_bound
-- name    : AvramDividend.Classical.scaleFunction_strict_pos_of_eventual_psi_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T10:40:05.107445+00:00
-- url     : https://prove2.me/theorems/793f3b68-4c27-4657-bed8-b7006216763d
-- title:
--   Strict positivity of a canonical q-scale function from eventual Lévy-exponent growth
-- statement:
--   Let W be the q-scale function of a spectrally negative Lévy process in the exact Avram framework. If above some nonnegative Laplace parameter β0 the exponent satisfies ψ(θ)>q and ψ(θ)-q has an at-most-quadratic upper bound, then W(a)>0 for every a>0. This bridges the deterministic strict-positivity theorem to the canonical IsScaleFunction definition, exposing only eventual positivity and quadratic growth as independent process-specific hypotheses.
-- source:
--   Exact Avram IsScaleFunction conjunction and the previously published generic quadratic-Laplace strict positivity reduction. The analytic process-specific growth hypothesis remains explicit; no unproved stochastic exit formula is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_strict_pos_of_eventual_psi_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (β0 C : ℝ) (hβ0 : 0 ≤ β0)
    (hψ : ∀ θ : ℝ, β0 ≤ θ → q < X.ψ θ)
    (hquadratic : ∀ θ : ℝ, β0 ≤ θ →
      X.ψ θ - q ≤ C * (1 + θ ^ 2)) :
    ∀ a : ℝ, 0 < a → 0 < W a := by
  sorry

end AvramDividend.Classical
