-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_jacobi_partial_momentum_two
-- name    : BirkhoffGlobalSection.jacobi_partial_momentum_two
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T19:09:31.742606+00:00
-- url     : https://prove2.me/theorems/6756f5ac-f997-46e0-a818-73dffa49e58a
-- title:
--   Second momentum derivative of the Jacobi Hamiltonian
-- statement:
--   At a point where the Jacobi Hamiltonian is differentiable, its partial derivative in the second momentum coordinate is $p_2+q_1$. The gravitational terms depend only on the position coordinates.
-- source:
--   Momentum differentiation of the rotating-frame Jacobi Hamiltonian, Joung--van Koert equation (1.1), https://arxiv.org/abs/2407.19159v3.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- Second momentum partial derivative of the Jacobi Hamiltonian, at a point
where the totalized potential is differentiable. -/
theorem jacobi_partial_momentum_two (μ : ℝ) (s : Phase)
    (hdiff : DifferentiableAt ℝ (jacobiHamiltonian μ) s) :
    partialDerivative (jacobiHamiltonian μ) s 3 = s 3 + s 0 := by sorry

end BirkhoffGlobalSection
