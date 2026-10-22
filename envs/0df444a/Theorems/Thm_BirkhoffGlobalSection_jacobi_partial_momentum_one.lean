-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_jacobi_partial_momentum_one
-- name    : BirkhoffGlobalSection.jacobi_partial_momentum_one
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T19:09:24.36995+00:00
-- url     : https://prove2.me/theorems/f9faf324-70a6-4ee9-b423-e76430186e6b
-- title:
--   First momentum derivative of the Jacobi Hamiltonian
-- statement:
--   At a point where the Jacobi Hamiltonian is differentiable, its partial derivative in the first momentum coordinate is $p_1-q_2$. The differentiability hypothesis ensures that the totalized potential does not silently replace an undefined Fréchet derivative by zero.
-- source:
--   Momentum differentiation of the rotating-frame Jacobi Hamiltonian, Joung--van Koert equation (1.1), https://arxiv.org/abs/2407.19159v3.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- First momentum partial derivative of the Jacobi Hamiltonian, at a point
where the totalized potential is differentiable. -/
theorem jacobi_partial_momentum_one (μ : ℝ) (s : Phase)
    (hdiff : DifferentiableAt ℝ (jacobiHamiltonian μ) s) :
    partialDerivative (jacobiHamiltonian μ) s 2 = s 2 - s 1 := by sorry

end BirkhoffGlobalSection
