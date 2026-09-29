-- Prove2me | Theorems.Thm_DiazModulus_recip_pi_exp_axis_shape
-- name    : DiazModulus.recip_pi_exp_axis_shape
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-13T10:45:51.469052+00:00
-- url     : https://prove2.me/theorems/2149ee8c-86ea-4a64-b101-0277b79b6ae7
-- title:
--   The two axis shapes of $e^{\gamma/(i\pi)}$
-- statement:
--   For $\gamma \neq 0$ put $\lambda = \gamma/(i\pi)$.
--
--   - If $\gamma$ is real, then $\lambda$ is purely imaginary and $|e^{\lambda}| = 1$.
--   - If $\gamma$ is purely imaginary, then $\lambda$ is a non-zero real, so $e^{\lambda}$ is real and $e^{\lambda} \neq 1$.
--
--   No algebraicity of $\gamma$ is assumed.
--
--   **What it is for.** These are the elementary facts behind the two children of `DiazModulus.recip_pi_not_log`. On the real-$\gamma$ half, a hypothetical algebraic value of $e^{\lambda}$ would be an algebraic number of modulus one; `DiazModulus.recip_pi_exp_value_not_root_of_unity` already rules out roots of unity there. On the imaginary-$\gamma$ half it would be a real algebraic number different from $1$.
--
--   **Not claimed.** No transcendence. The statement is elementary and recorded so that both shapes can be cited.
-- source:
--   Elementary.

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus
theorem recip_pi_exp_axis_shape :
    ∀ γ : ℂ, γ ≠ 0 →
      (γ.im = 0 → ‖Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I))‖ = 1) ∧
      (γ.re = 0 → (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I))).im = 0 ∧ Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I)) ≠ 1) := by sorry
end DiazModulus
