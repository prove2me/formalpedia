-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_partial_derivative_eq_update_deriv
-- name    : BirkhoffGlobalSection.partial_derivative_eq_update_deriv
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T22:17:16.892415+00:00
-- url     : https://prove2.me/theorems/eb2a9de2-4600-4e45-8af6-ebd6b4840025
-- title:
--   Fréchet partial derivative as a coordinate-line derivative
-- statement:
--   For a real-valued function on four-dimensional real phase space that is differentiable at a point, its Fréchet derivative in a standard coordinate direction equals the one-variable derivative obtained by varying just that coordinate. This bridges the function-update coordinate line to the `partialDerivative` definition.
-- source:
--   For the Hamiltonian calculation: Joung--van Koert, equation (1.1), https://arxiv.org/abs/2407.19159v3. The derivative bridge is the standard chain rule for an affine coordinate line.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- A Fréchet partial derivative equals the ordinary derivative along the
corresponding coordinate line in four-dimensional phase space. -/
theorem partial_derivative_eq_update_deriv
    (F : Phase → ℝ) (s : Phase) (i : Fin 4)
    (hdiff : DifferentiableAt ℝ F s) :
    partialDerivative F s i =
      deriv (fun t : ℝ => F (Function.update s i t)) (s i) := by sorry

end BirkhoffGlobalSection
