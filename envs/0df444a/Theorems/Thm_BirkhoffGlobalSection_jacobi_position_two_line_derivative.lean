-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_jacobi_position_two_line_derivative
-- name    : BirkhoffGlobalSection.jacobi_position_two_line_derivative
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T22:51:17.756807+00:00
-- url     : https://prove2.me/theorems/bea8a951-e046-443d-b10b-3111c171fcf6
-- title:
--   Derivative of the Jacobi Hamiltonian along the vertical position line
-- statement:
--   Fix a collision-free phase point. Vary only its second position coordinate while holding the other three coordinates fixed. The resulting one-variable Jacobi Hamiltonian has derivative equal to minus the second momentum plus the vertical components of the two inverse-distance forces.
-- source:
--   Jacobi Hamiltonian of the planar circular restricted three-body problem, via elementary differential calculus.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- Differentiate the Jacobi Hamiltonian on a vertical position coordinate line. -/
theorem jacobi_position_two_line_derivative (μ : ℝ) (s : Phase)
    (hfree : collisionFree μ s) :
    HasDerivAt (fun t : ℝ => jacobiHamiltonian μ (Function.update s 1 t))
      (-s 2 + (1 - μ) * (s 1) /
        (Real.sqrt ((s 0 + μ) ^ 2 + (s 1) ^ 2)) ^ 3 +
        μ * (s 1) /
        (Real.sqrt ((s 0 - 1 + μ) ^ 2 + (s 1) ^ 2)) ^ 3) (s 1) := by sorry

end BirkhoffGlobalSection
