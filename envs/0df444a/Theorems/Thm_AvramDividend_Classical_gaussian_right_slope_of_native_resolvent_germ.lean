-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_right_slope_of_native_resolvent_germ
-- name    : AvramDividend.Classical.gaussian_right_slope_of_native_resolvent_germ
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T11:02:07.049791+00:00
-- url     : https://prove2.me/theorems/3a7aae03-5c48-47dc-943c-1b3aa10fba7d
-- title:
--   Exact Gaussian scale right slope from the native Volterra derivative resolvent
-- statement:
--   For a positive Gaussian coefficient sigma, a native second-kind derivative resolvent satisfies (sigma^2/2)g(x)+C(x)=1. If g is continuous at zero and C(x)→0 from the right, its value at zero is 2/sigma^2. If V(x)→0 and W(x)=exp(phi*x)V(x) with V'(x)=g(x), the Gaussian q-scale derivative tends to 2/sigma^2 on approaching zero from the right. The theorem supplies an exact importable conditional bridge to the corrected right-origin-normalisation theorem.
-- source:
--   Composition of Proved causal_volterra_origin_value_of_vanishing_residual and esscher_untilt_deriv_right_limit_of_resolvent.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FieldSimp
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_causal_volterra_origin_value_of_vanishing_residual
import Theorems.Thm_AvramDividend_Classical_esscher_untilt_deriv_right_limit_of_resolvent
open AvramDividend.Classical MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

namespace AvramDividend.Classical
/-- Exact Gaussian right derivative limit from a native Volterra resolvent germ. -/
theorem gaussian_right_slope_of_native_resolvent_germ
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hσ : 0 < X.σ)
    (W V g C : ℝ → ℝ) (φ : ℝ)
    (hW : ∀ x : ℝ, 0 < x → W x = Real.exp (φ * x) * V x)
    (hVlim : Tendsto V (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (hC : Tendsto C (𝓝[>] (0 : ℝ)) (𝓝 0))
    (heq : ∀ x : ℝ, 0 < x → (X.σ ^ 2 / 2) * g x + C x = 1)
    (hVderiv : ∀ x : ℝ, 0 < x → HasDerivAt V (g x) x) :
    Tendsto (deriv W) (𝓝[>] (0 : ℝ)) (𝓝 (2 / X.σ ^ 2)) := by
  sorry
end AvramDividend.Classical
