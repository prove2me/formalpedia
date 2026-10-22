-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_leviCivita_flow_antipodally_equivariant
-- name    : BirkhoffGlobalSection.leviCivita_flow_antipodally_equivariant
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T23:11:42.777413+00:00
-- url     : https://prove2.me/theorems/78761a4c-5114-4e54-9237-9c8e11f55974
-- title:
--   Antipodal equivariance of the regularized flow
-- statement:
--   The regularized flow commutes with the antipodal deck transformation.
--
--   Fix $0<\mu<1$ and a Jacobi energy $-c$ below the first critical value. Let $\Sigma_{\mu,c}$ be the selected Levi-Civita component around the primary of mass $1-\mu$, with points $s=(z,w)\in\mathbb R^4$, $z=(z_1,z_2)$, $w=(w_1,w_2)$. Let $\varphi$ be a continuous flow on $\Sigma_{\mu,c}$ whose time derivative at $t=0$ is the Hamiltonian vector field of the regularized Hamiltonian $K_{\mu,c}$. Then for all $t\in\mathbb R$ and all $s\in\Sigma_{\mu,c}$,
--   $$
--   \varphi_t(-s)=-\varphi_t(s).
--   $$
--
--   The Hamiltonian $K_{\mu,c}$ is even, so its Hamiltonian vector field is odd, and $t\mapsto-\varphi_t(s)$ is again an integral curve in the antipodally invariant component. Uniqueness of integral curves of the smooth vector field on the compact component then gives the identity. This is the equivariance under which the Levi-Civita cover descends to the Moser-regularized quotient.
-- source:
--   Joung--van Koert, https://arxiv.org/abs/2407.19159v3, Section 2 and Proposition 2.4 (the Levi-Civita double cover and its antipodal deck transformation).

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem leviCivita_flow_antipodally_equivariant (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) :
    IsAntipodallyEquivariantFlow μ c φ := by sorry

end BirkhoffGlobalSection
