-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_jacobi_critical_momentum
-- name    : BirkhoffGlobalSection.jacobi_critical_momentum
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T19:05:17.061683+00:00
-- url     : https://prove2.me/theorems/3d7938c1-9022-4f3d-9811-cbc6caa4607d
-- title:
--   Momentum at a Jacobi equilibrium
-- statement:
--   At a critical point of the Jacobi Hamiltonian, the two momentum derivatives vanish. Thus the first momentum coordinate equals the second position coordinate and the second momentum coordinate is the negative of the first position coordinate.
-- source:
--   Equilibrium equations of the Jacobi Hamiltonian (equation (1.1)) in Joung--van Koert, https://arxiv.org/abs/2407.19159v3; standard triangular Lagrange-point calculation.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- The momentum derivatives of the Jacobi Hamiltonian vanish only at the
rotating-frame momentum determined by the position. -/
theorem jacobi_critical_momentum (μ : ℝ) (s : Phase)
    (hcrit : isCriticalPoint (jacobiHamiltonian μ) s) :
    s 2 = s 1 ∧ s 3 = -s 0 := by sorry

end BirkhoffGlobalSection
