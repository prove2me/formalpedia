-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_birkhoff_near_shooting_family
-- name    : BirkhoffGlobalSection.birkhoff_near_shooting_family
-- status  : Open
-- author  : @Mazecto
-- created : 2026-09-25T07:48:32.111507+00:00
-- url     : https://prove2.me/theorems/6ab47345-b305-470d-b03c-39efae315b6a
-- title:
--   Birkhoff's near shooting family $\Gamma_2$ as a curve in the $(\sigma,\eta)$ rectangle
-- statement:
--   Fix $0<\mu<1$ and a Jacobi energy $-c$ below the first critical value. Let $\Sigma_{\mu,c}$ be the selected Levi-Civita component around the primary $P$ of mass $1-\mu$, with points $s=(z,w)\in\mathbb R^4$, and let $\varphi$ be a continuous flow on $\Sigma_{\mu,c}$ whose time derivative at $t=0$ is the Hamiltonian vector field of the regularized Hamiltonian $K_{\mu,c}$. Write $x(s)=(x_1,x_2)=2z^2$ for the physical position relative to $P$, $v(s)$ for the rotating-frame (Jacobi) velocity, and $(\sigma(s),\eta(s))=\bigl(v_2/|v|,\,-x_2\bigr)$ for Birkhoff's shooting coordinates. Let $R=[-1,1]\times[0,1]$.
--
--   **Near family.** There are a curve $\Gamma:[-1,1]\to R$ and a number $\alpha$ with the following properties.
--
--   1. $\Gamma$ is continuous, with
--   $$
--   -1<\alpha<-\tfrac{\sqrt2}{2},\qquad \Gamma(-1)=(\alpha,0),\qquad \Gamma(1)=\bigl(\tfrac{\sqrt2}{2},0\bigr).
--   $$
--   2. For every $-1<\lambda<1$, $\Gamma(\lambda)$ lies in the open part $|\sigma|<1$, $\eta>0$ of $R$ and is realized by a trajectory. That is, there are $s\in\Sigma_{\mu,c}$ and $\tau>0$ such that:
--      - $z_2(s)=0$, $w_1(s)=0$ and $z_1(s)\ne0$, so $s$ leaves the positive $x_1$-axis perpendicularly, on the side of $P$ facing the other primary;
--      - $x_2(\varphi_t s)<0$ for $-\tau<t<0$;
--      - $t\mapsto x_1(\varphi_t s)$ is strictly increasing on $[-\tau,0]$;
--      - at $t=-\tau$ the trajectory is on the line $x_1=0$ with $v_1>0$, and $(\sigma,\eta)(\varphi_{-\tau}s)=\Gamma(\lambda)$.
--
--   This is the curve $\Gamma_2$ of Birkhoff's shooting argument. It is traced by the perpendicular starts on the near side, followed backward in time to their first crossing of the vertical line through $P$. As the start point tends to $P$, the crossing tends to the collision direction $\sigma=\sqrt2/2$. At the other end the backward trajectory runs into collision from a direction with $\sigma<-\sqrt2/2$. Together with the far family and the crossing lemma for interlaced arcs, this produces the symmetric half of the retrograde orbit.
--
--   **Formalization Note** The family is reparametrized by $\lambda\in[-1,1]$. Only its values, not its parametrization, matter.
-- source:
--   Liu--Salomao, Finite energy foliations in the restricted three-body problem, https://arxiv.org/abs/2506.17867v2, Section 5, proof of Theorem 5.1 (pp. 30-31): the curves Gamma_1, Gamma_2 and their endpoints on the bottom side at velocity angles +-pi/4; after G. D. Birkhoff, The restricted problem of three bodies, Rend. Circ. Mat. Palermo 39 (1915), Sections 16-18 (Collected Mathematical Papers Vol. 1, pp. 731-741).

import Definitions.Def_BirkhoffShootingCoordinates

namespace BirkhoffGlobalSection

theorem birkhoff_near_shooting_family (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) :
    ∃ Γ : ℝ → ℝ × ℝ, ∃ α : ℝ, -1 < α ∧ α < -(Real.sqrt 2 / 2) ∧
      ContinuousOn Γ (Set.Icc (-1) 1) ∧
      Γ (-1) = (α, 0) ∧ Γ 1 = (Real.sqrt 2 / 2, 0) ∧
      (∀ s ∈ Set.Icc (-1 : ℝ) 1,
        -1 ≤ (Γ s).1 ∧ (Γ s).1 ≤ 1 ∧ 0 ≤ (Γ s).2 ∧ (Γ s).2 ≤ 1) ∧
      ∀ s ∈ Set.Ioo (-1 : ℝ) 1, |(Γ s).1| < 1 ∧ 0 < (Γ s).2 ∧
        ∃ x : LeftEnergyState μ c, ∃ τ : ℝ, 0 < τ ∧
          (x : Phase) 1 = 0 ∧ (x : Phase) 2 = 0 ∧ (x : Phase) 0 ≠ 0 ∧
          (∀ t ∈ Set.Ioo (-τ) 0,
            relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 1 < 0) ∧
          StrictMonoOn
            (fun t : ℝ => relativePosition μ ((φ t x : LeftEnergyState μ c) : Phase) 0)
            (Set.Icc (-τ) 0) ∧
          relativePosition μ ((φ (-τ) x : LeftEnergyState μ c) : Phase) 0 = 0 ∧
          0 < jacobiVelocity
            (leviCivitaToJacobi μ ((φ (-τ) x : LeftEnergyState μ c) : Phase)) 0 ∧
          shootingCoordinates μ ((φ (-τ) x : LeftEnergyState μ c) : Phase) = Γ s := by sorry

end BirkhoffGlobalSection
