-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_leviCivita_flow_q2_reversible
-- name    : BirkhoffGlobalSection.leviCivita_flow_q2_reversible
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T23:11:36.248781+00:00
-- url     : https://prove2.me/theorems/6c8e1935-85c0-41a2-8780-8ca71ac20473
-- title:
--   Time-reversal symmetry of the regularized flow
-- statement:
--   The regularized flow is time-reversible with respect to the lift of the reflection across the line of primaries.
--
--   Fix $0<\mu<1$ and a Jacobi energy $-c$ below the first critical value. Let $\Sigma_{\mu,c}$ be the selected Levi-Civita component around the primary of mass $1-\mu$, with points $s=(z,w)\in\mathbb R^4$, $z=(z_1,z_2)$, $w=(w_1,w_2)$. Let $\varphi$ be a continuous flow on $\Sigma_{\mu,c}$ whose time derivative at $t=0$ is the Hamiltonian vector field of the regularized Hamiltonian $K_{\mu,c}$. Let $\rho(z_1,z_2,w_1,w_2)=(z_1,-z_2,-w_1,w_2)$, i.e. $\rho(z,w)=(\bar z,-\bar w)$. This is the Levi-Civita lift of the Jacobi reflection $R(q,p)=(\bar q,-\bar p)$. If $s,s'\in\Sigma_{\mu,c}$ with $s'=\rho(s)$, then for all $t\in\mathbb R$,
--   $$
--   \varphi_{-t}(s')=\rho\bigl(\varphi_t(s)\bigr).
--   $$
--
--   Since $K_{\mu,c}\circ\rho=K_{\mu,c}$ and $\rho$ is anti-symplectic, $t\mapsto\rho(\varphi_{-t}(s))$ is an integral curve, and uniqueness gives the identity. This time-reversal symmetry underlies the $q_2$-symmetric periodic orbits of Birkhoff's shooting method: a trajectory meeting the fixed set of $\rho$ or $-\rho$ twice closes up.
--
--   **Formalization Note** The map $\rho$ is written with the platform's `jacobiQ₂Reflection`, whose coordinate formula coincides with the Levi-Civita lift.
-- source:
--   Liu--Salomao, Finite energy foliations in the restricted three-body problem, https://arxiv.org/abs/2506.17867v2, Section 5 (q2-symmetric orbits and the reflection symmetry of the rotating Kepler/PCR3BP Hamiltonian); lifted through the Levi-Civita map of Joung--van Koert, https://arxiv.org/abs/2407.19159v3, Section 2.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem leviCivita_flow_q2_reversible (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) :
    ∀ t : ℝ, ∀ s₁ s₂ : LeftEnergyState μ c,
      (s₂ : Phase) = jacobiQ₂Reflection (s₁ : Phase) →
        ((φ (-t) s₂ : LeftEnergyState μ c) : Phase) =
          jacobiQ₂Reflection ((φ t s₁ : LeftEnergyState μ c) : Phase) := by sorry

end BirkhoffGlobalSection
