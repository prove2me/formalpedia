-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_birkhoff_far_shooting_family
-- name    : BirkhoffGlobalSection.birkhoff_far_shooting_family
-- status  : Open
-- author  : @Mazecto
-- created : 2026-09-25T07:48:27.815497+00:00
-- url     : https://prove2.me/theorems/1afa9034-87d8-431c-8306-2424718888f9
-- title:
--   Birkhoff's far shooting family $\Gamma_1$ as a curve in the $(\sigma,\eta)$ rectangle
-- statement:
--   Fix $0<\mu<1$ and a Jacobi energy $-c$ below the first critical value. Let $\Sigma_{\mu,c}$ be the selected Levi-Civita component around the primary $P$ of mass $1-\mu$, with points $s=(z,w)\in\mathbb R^4$, and let $\varphi$ be a continuous flow on $\Sigma_{\mu,c}$ whose time derivative at $t=0$ is the Hamiltonian vector field of the regularized Hamiltonian $K_{\mu,c}$. Write $x(s)=(x_1,x_2)=2z^2$ for the physical position relative to $P$, $v(s)$ for the rotating-frame (Jacobi) velocity, and $(\sigma(s),\eta(s))=\bigl(v_2/|v|,\,-x_2\bigr)$ for Birkhoff's shooting coordinates. Let $R=[-1,1]\times[0,1]$.
--
--   **Far family.** There is a continuous curve $\Gamma':[-1,1]\to R$ with the following properties.
--
--   1. It starts at
--   $$
--   \Gamma'(-1)=\bigl(-\tfrac{\sqrt2}{2},0\bigr).
--   $$
--   It ends either on a vertical side ($\sigma=\pm1$) strictly above the bottom, or on the bottom at a point with $\sigma>\sqrt2/2$.
--   2. For every $-1<\lambda<1$, $\eta(\Gamma'(\lambda))>0$ and $\Gamma'(\lambda)$ is realized by a trajectory. That is, there are $s\in\Sigma_{\mu,c}$ and $\tau>0$ such that:
--      - $z_1(s)=0$, $w_2(s)=0$ and $z_2(s)\ne0$, so $s$ leaves the negative $x_1$-axis perpendicularly, on the side of $P$ away from the other primary;
--      - $x_2(\varphi_u s)<0$ for $0<u<\tau$;
--      - $u\mapsto x_1(\varphi_u s)$ is strictly increasing on $[0,\tau]$;
--      - at $u=\tau$ the trajectory is on the line $x_1=0$ with $v_1>0$, and $(\sigma,\eta)(\varphi_\tau s)=\Gamma'(\lambda)$.
--
--   This is the curve $\Gamma_1$ of Birkhoff's shooting argument. It is traced by the perpendicular starts on the far side, followed forward in time to their first crossing of the vertical line through $P$. As the start point tends to $P$, the crossing tends to the collision direction $\sigma=-\sqrt2/2$. The curve is followed until it first leaves the open rectangle, which happens either at a tangency with the vertical line or at a collision from a direction with $\sigma>\sqrt2/2$. It interlaces with the near family, and their intersection gives the symmetric half of the retrograde orbit.
--
--   **Formalization Note** The family is reparametrized by $\lambda\in[-1,1]$. Only its values, not its parametrization, matter.
-- source:
--   Liu--Salomao, Finite energy foliations in the restricted three-body problem, https://arxiv.org/abs/2506.17867v2, Section 5, proof of Theorem 5.1 (pp. 30-31): the curves Gamma_1, Gamma_2 and their endpoints on the bottom side at velocity angles +-pi/4; after G. D. Birkhoff, The restricted problem of three bodies, Rend. Circ. Mat. Palermo 39 (1915), Sections 16-18 (Collected Mathematical Papers Vol. 1, pp. 731-741).

import Definitions.Def_BirkhoffShootingCoordinates

namespace BirkhoffGlobalSection

theorem birkhoff_far_shooting_family (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) :
    ∃ Γ : ℝ → ℝ × ℝ,
      ContinuousOn Γ (Set.Icc (-1) 1) ∧
      Γ (-1) = (-(Real.sqrt 2 / 2), 0) ∧
      ((((Γ 1).1 = -1 ∨ (Γ 1).1 = 1) ∧ 0 < (Γ 1).2) ∨
        ((Γ 1).2 = 0 ∧ Real.sqrt 2 / 2 < (Γ 1).1)) ∧
      (∀ t ∈ Set.Icc (-1 : ℝ) 1,
        -1 ≤ (Γ t).1 ∧ (Γ t).1 ≤ 1 ∧ 0 ≤ (Γ t).2 ∧ (Γ t).2 ≤ 1) ∧
      ∀ t ∈ Set.Ioo (-1 : ℝ) 1, 0 < (Γ t).2 ∧
        ∃ x : LeftEnergyState μ c, ∃ τ : ℝ, 0 < τ ∧
          (x : Phase) 0 = 0 ∧ (x : Phase) 3 = 0 ∧ (x : Phase) 1 ≠ 0 ∧
          (∀ u ∈ Set.Ioo 0 τ,
            relativePosition μ ((φ u x : LeftEnergyState μ c) : Phase) 1 < 0) ∧
          StrictMonoOn
            (fun u : ℝ => relativePosition μ ((φ u x : LeftEnergyState μ c) : Phase) 0)
            (Set.Icc 0 τ) ∧
          relativePosition μ ((φ τ x : LeftEnergyState μ c) : Phase) 0 = 0 ∧
          0 < jacobiVelocity
            (leviCivitaToJacobi μ ((φ τ x : LeftEnergyState μ c) : Phase)) 0 ∧
          shootingCoordinates μ ((φ τ x : LeftEnergyState μ c) : Phase) = Γ t := by sorry

end BirkhoffGlobalSection
