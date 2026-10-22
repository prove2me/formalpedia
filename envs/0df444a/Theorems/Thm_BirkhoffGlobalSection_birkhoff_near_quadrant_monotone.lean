-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_birkhoff_near_quadrant_monotone
-- name    : BirkhoffGlobalSection.birkhoff_near_quadrant_monotone
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-25T08:51:57.612847+00:00
-- url     : https://prove2.me/theorems/18f1840c-d620-4de0-8747-8393d138a28f
-- title:
--   Birkhoff's near-side monotonicity: $\frac{d}{dt}(\dot x_1+2x_2)=\Omega_{x_1}<0$
-- statement:
--   Fix $0<\mu<1$ and a Jacobi energy $-c$ below the first critical value. Let $\Sigma_{\mu,c}$ be the selected Levi-Civita component around the primary $P$ of mass $1-\mu$, with points $s=(z,w)\in\mathbb R^4$. Let $\varphi$ be a continuous flow on $\Sigma_{\mu,c}$ whose time derivative at $t=0$ is the Hamiltonian vector field of the regularized Hamiltonian $K_{\mu,c}$. Write $x(s)=(x_1,x_2)=2z^2$ for the physical position relative to $P$, $v(s)$ for the rotating-frame (Jacobi) velocity, and $(\sigma,\eta)=(v_2/|v|,\,-x_2)$ for Birkhoff's shooting coordinates.
--
--   **Near quadrant lemma.** Let $s\in\Sigma_{\mu,c}$ satisfy $z_2(s)=w_1(s)=0\neq z_1(s)$, so that $s$ sits on the positive $x_1$-axis with velocity perpendicular to it. Let $\tau>0$, and assume that the backward trajectory stays in the open lower near quadrant,
--   $$
--   x_1(\varphi_t s)>0,\qquad x_2(\varphi_t s)<0\qquad(-\tau<t<0),
--   $$
--   and that $x_2(\varphi_{-\tau}s)<0$. Then:
--
--   1. $t\mapsto x_1(\varphi_t s)$ is strictly increasing on $[-\tau,0]$;
--   2. the Jacobi velocity at $\varphi_{-\tau}s$ has $v_1>0$.
--
--   This is Birkhoff's monotonicity argument for the near family. It rests on the identity $\frac{d}{dt}(v_1+2x_2)=\Omega_{x_1}$, together with the fact that $\Omega_{x_1}<0$ on the near half of the disk bounded by the inner Lagrange circle, which contains the selected component. The lemma supplies the monotone sweep and the transversal crossing for every member of the near family.
--
--   **Formalization Note** In Levi-Civita time the derivative of $v_1+2x_2$ is $4|z|^2\Omega_{x_1}$ on the energy level, and the derivative of $x_1$ is $4|z|^2v_1$.
-- source:
--   Liu--Salomao, Finite energy foliations in the restricted three-body problem, https://arxiv.org/abs/2506.17867v2, Section 5, proof of Theorem 5.1 (pp. 30-31): the curves Gamma_1, Gamma_2 traced by the perpendicular starts; after G. D. Birkhoff, The restricted problem of three bodies, Rend. Circ. Mat. Palermo 39 (1915), Sections 16-18 (Collected Mathematical Papers Vol. 1, pp. 731-741).

import Definitions.Def_BirkhoffShootingCoordinates

namespace BirkhoffGlobalSection

theorem birkhoff_near_quadrant_monotone (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c)) (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (x : LeftEnergyState μ c) (τ : ℝ) (hτ : 0 < τ)
    (hx1 : (x : Phase) 1 = 0) (hx2 : (x : Phase) 2 = 0) (hx0 : (x : Phase) 0 ≠ 0)
    (hq : ∀ t ∈ Set.Ioo (-τ) 0,
      0 < relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 0 ∧
      relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 1 < 0)
    (hend : relativePosition μ ((φ (-τ) x : LeftEnergyState μ c) : Phase) 1 < 0) :
    StrictMonoOn
        (fun t : ℝ => relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 0)
        (Set.Icc (-τ) 0) ∧
      0 < jacobiVelocity
        (leviCivitaToJacobi μ ((φ (-τ) x : LeftEnergyState μ c) : Phase)) 0 := by sorry

end BirkhoffGlobalSection
