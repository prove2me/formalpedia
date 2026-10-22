-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_birkhoff_shooting_symmetric_half_orbit
-- name    : BirkhoffGlobalSection.birkhoff_shooting_symmetric_half_orbit
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T23:11:38.802116+00:00
-- url     : https://prove2.me/theorems/79844180-cb97-42be-aadb-c8556ea447c2
-- title:
--   Birkhoff's shooting: a symmetric retrograde half-orbit
-- statement:
--   This is the output of Birkhoff's shooting argument: a symmetric half of the retrograde orbit.
--
--   Fix $0<\mu<1$ and a Jacobi energy $-c$ below the first critical value. Let $\Sigma_{\mu,c}$ be the selected Levi-Civita component around the primary of mass $1-\mu$, with points $s=(z,w)\in\mathbb R^4$, $z=(z_1,z_2)$, $w=(w_1,w_2)$. Let $\varphi$ be a continuous flow on $\Sigma_{\mu,c}$ whose time derivative at $t=0$ is the Hamiltonian vector field of the regularized Hamiltonian $K_{\mu,c}$. Write $x(s)=(x_1(s),x_2(s))=(2(z_1^2-z_2^2),\,4z_1z_2)$ for the physical position relative to the first primary, i.e. $x=2z^2$.
--
--   There exist a point $s_0\in\Sigma_{\mu,c}$ and a time $\tau>0$ such that the following hold.
--
--   1. **Perpendicular start on the far side.** $z_1(s_0)=0$, $w_2(s_0)=0$ and $z_2(s_0)\neq0$. Physically, the satellite starts on the negative $x_1$-axis, away from the second primary, with velocity perpendicular to the axis.
--   2. **Perpendicular arrival on the near side.** The point $s_1=\varphi_\tau(s_0)$ satisfies $z_2(s_1)=0$, $w_1(s_1)=0$ and $z_1(s_1)\neq0$. Physically, it arrives perpendicularly on the positive $x_1$-axis, between the primaries.
--   3. **Lower half-plane.** $x_2(\varphi_t(s_0))<0$ for all $0<t<\tau$.
--   4. **Monotone sweep.** $t\mapsto x_1(\varphi_t(s_0))$ is strictly increasing on $[0,\tau]$.
--
--   In Liu–Salomão's account of Birkhoff's proof, $\Gamma_1$ and $\Gamma_2$ are the curves traced, in the (velocity angle, $q_2$) rectangle, by the families of trajectories leaving the $q_1$-axis perpendicularly from the left and from the right. These curves are traced until the trajectories reach the $q_2$-axis in the lower half-plane with $\dot q_1>0$. An intersection of $\Gamma_1$ and $\Gamma_2$ joins two such arcs into one trajectory from the left axis to the right axis, and this is exactly the half-orbit above. Reflecting it across the $q_1$-axis closes it into Birkhoff's $q_2$-symmetric retrograde orbit.
--
--   **Formalization Note** The perpendicular crossings are stated in Levi-Civita coordinates. On the $q_1$-axis the fixed points of the Jacobi reflection $(q_1,q_2,p_1,p_2)\mapsto(q_1,-q_2,-p_1,p_2)$ lift to $\{z_1=w_2=0\}$ on the negative side and $\{z_2=w_1=0\}$ on the positive side.
-- source:
--   Liu--Salomao, Finite energy foliations in the restricted three-body problem, https://arxiv.org/abs/2506.17867v2, Section 5, proof of Theorem 5.1 (pp. 30-31): the curves Gamma_1, Gamma_2 and their intersection; after G. D. Birkhoff, The restricted problem of three bodies, Rend. Circ. Mat. Palermo 39 (1915).

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem birkhoff_shooting_symmetric_half_orbit (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) :
    ∃ x : LeftEnergyState μ c, ∃ τ : ℝ, 0 < τ ∧
      (x : Phase) 0 = 0 ∧ (x : Phase) 3 = 0 ∧ (x : Phase) 1 ≠ 0 ∧
      ((φ τ x : LeftEnergyState μ c) : Phase) 1 = 0 ∧
      ((φ τ x : LeftEnergyState μ c) : Phase) 2 = 0 ∧
      ((φ τ x : LeftEnergyState μ c) : Phase) 0 ≠ 0 ∧
      (∀ t ∈ Set.Ioo 0 τ,
        relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 1 < 0) ∧
      StrictMonoOn
        (fun t : ℝ => relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 0)
        (Set.Icc 0 τ) := by sorry

end BirkhoffGlobalSection
