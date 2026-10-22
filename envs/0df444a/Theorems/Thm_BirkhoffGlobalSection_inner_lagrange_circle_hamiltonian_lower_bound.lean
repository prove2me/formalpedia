-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_circle_hamiltonian_lower_bound
-- name    : BirkhoffGlobalSection.inner_lagrange_circle_hamiltonian_lower_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T18:47:10.817743+00:00
-- url     : https://prove2.me/theorems/7f862451-af12-454a-bf3e-3fd566a7f4ef
-- title:
--   Energy lower bound on the circle through the inner equilibrium
-- statement:
--   Fix $0<\mu<1$ and an inner collinear Lagrange equilibrium $L_1$. At every Levi-Civita phase point whose physical position is on the circle about the left primary through $L_1$, the zero-offset regularized Hamiltonian is at least $|z|^2 H_\mu(L_1)$. This combines a maximum principle for the effective potential on that circle with nonnegativity of the completed momentum square.
-- source:
--   Joung--van Koert, Proposition 2.4 and equation (2.2), https://arxiv.org/abs/2407.19159v3, PDF pp. 6–7; the standard subcritical Hill-region neck argument.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- At the position circle through the inner collinear equilibrium, its
effective potential is maximal. Completing the momentum squares gives this
lower bound on the zero-offset Levi-Civita Hamiltonian. -/
theorem inner_lagrange_circle_hamiltonian_lower_bound (μ : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (L : Phase)
    (hL : IsInnerLagrangePoint μ L) (s : Phase)
    (hr : ((leviCivitaPosition μ s) 0 + μ) ^ 2 +
      ((leviCivitaPosition μ s) 1) ^ 2 = (L 0 + μ) ^ 2) :
    zNormSq s * jacobiHamiltonian μ L ≤ leviCivitaHamiltonian μ 0 s := by sorry

end BirkhoffGlobalSection
