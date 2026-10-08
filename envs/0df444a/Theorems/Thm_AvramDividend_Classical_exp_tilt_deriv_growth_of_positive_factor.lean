-- Prove2me | Theorems.Thm_AvramDividend_Classical_exp_tilt_deriv_growth_of_positive_factor
-- name    : AvramDividend.Classical.exp_tilt_deriv_growth_of_positive_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T18:24:26.86429+00:00
-- url     : https://prove2.me/theorems/297d9d2c-9032-4057-b186-ac93182aea7d
-- title:
--   Exponential Esscher tilt produces a derivative diverging to positive infinity
-- statement:
--   Let φ>0 and V be differentiable on (0,∞), have nonnegative ordinary derivative there, and be eventually bounded below by a strictly positive constant c. Then the derivative of exp(φx)V(x) tends to +∞ as x→∞. The exact product-rule identity is (exp(φx)V(x))'=exp(φx)(φ V(x)+V'(x)). This is the critical elementary analytic bridge that converts eventual positivity and monotonicity of an Esscher-tilted scale factor into growth of the original q-scale derivative, without differentiating a mere asymptotic equivalence.
-- source:
--   Pinned Mathlib APIs: HasDerivAt.exp (Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean:304), HasDerivAt.mul (Mathlib/Analysis/Calculus/Deriv/Mul.lean:266), tendsto_const_mul_atTop_of_pos, Real.tendsto_exp_atTop, and Filter.tendsto_atTop_mono'. Formally differentiate the factorization, lower bound W' by φ*c*exp(φx), and transfer its divergence to W'. This is an abstract calculus child, NOT a proof that the canonical Levy q-scale function admits the Esscher representation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical Filter Set
open scoped ENNReal

namespace AvramDividend.Classical
theorem exp_tilt_deriv_growth_of_positive_factor
    (φ c : ℝ) (hφ : 0 < φ) (hc : 0 < c) (V : ℝ → ℝ)
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ V x)
    (hderiv : ∀ x : ℝ, 0 < x → 0 ≤ deriv V x)
    (hbound : ∀ᶠ x : ℝ in Filter.atTop, c ≤ V x) :
    Filter.Tendsto (deriv (fun x : ℝ => Real.exp (φ * x) * V x))
      Filter.atTop Filter.atTop := by
  sorry
end AvramDividend.Classical
