-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_birkhoff_near_crossing_curve
-- name    : BirkhoffGlobalSection.birkhoff_near_crossing_curve
-- status  : Open
-- author  : @Mazecto
-- created : 2026-09-25T08:52:02.095265+00:00
-- url     : https://prove2.me/theorems/a7380b8e-b53d-4844-8433-dcdbb8d544b8
-- title:
--   Birkhoff's near family: continuous crossing curve with collision limits
-- statement:
--   Fix $0<\mu<1$ and a Jacobi energy $-c$ below the first critical value. Let $\Sigma_{\mu,c}$ be the selected Levi-Civita component around the primary $P$ of mass $1-\mu$, with points $s=(z,w)\in\mathbb R^4$. Let $\varphi$ be a continuous flow on $\Sigma_{\mu,c}$ whose time derivative at $t=0$ is the Hamiltonian vector field of the regularized Hamiltonian $K_{\mu,c}$. Write $x(s)=(x_1,x_2)=2z^2$ for the physical position relative to $P$, $v(s)$ for the rotating-frame (Jacobi) velocity, and $(\sigma,\eta)=(v_2/|v|,\,-x_2)$ for Birkhoff's shooting coordinates.
--
--   **Near family as a crossing curve.** There are $b>0$, a number $\alpha$ with $-1<\alpha<-\sqrt2/2$, states $S(r)$ and times $T(r)$, for $0<r<b$, with the following properties.
--
--   1. $S(r)$ starts perpendicularly on the near half-axis: $z_2=w_1=0\ne z_1$.
--   2. $T(r)>0$. On $(-T(r),0)$ the backward trajectory stays in the open quadrant $\{x_1>0,\ x_2<0\}$. At $t=-T(r)$ it reaches the vertical line $x_1=0$ strictly below the axis.
--   3. The crossing coordinates
--   $$
--   F(r)=(\sigma,\eta)\bigl(\varphi_{-T(r)}S(r)\bigr)
--   $$
--   depend continuously on $r\in(0,b)$, and
--   $$
--   \lim_{r\to0^+}F(r)=\bigl(\tfrac{\sqrt2}{2},0\bigr),\qquad \lim_{r\to b^-}F(r)=(\alpha,0).
--   $$
--
--   This is the analytic content of Birkhoff's near family $\Gamma_2$. The continuity comes from the transversality of the first crossing. The limit at $r\to0$ is the collision limit at angle $\pi/4$. The limit at $r\to b$ describes the member of the family that runs into collision, arriving from a direction strictly inside the lower near quadrant.
--
--   **Formalization Note** The states $S(r)$ are only required to exist; in Birkhoff's construction $S(r)$ is the perpendicular start at distance $2r^2$ from $P$.
-- source:
--   Liu--Salomao, Finite energy foliations in the restricted three-body problem, https://arxiv.org/abs/2506.17867v2, Section 5, proof of Theorem 5.1 (pp. 30-31): the curves Gamma_1, Gamma_2 traced by the perpendicular starts; after G. D. Birkhoff, The restricted problem of three bodies, Rend. Circ. Mat. Palermo 39 (1915), Sections 16-18 (Collected Mathematical Papers Vol. 1, pp. 731-741).

import Definitions.Def_BirkhoffShootingCoordinates
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic

namespace BirkhoffGlobalSection

theorem birkhoff_near_crossing_curve (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) :
    ∃ b : ℝ, 0 < b ∧ ∃ α : ℝ, -1 < α ∧ α < -(Real.sqrt 2 / 2) ∧
      ∃ S : ℝ → LeftEnergyState μ c, ∃ T : ℝ → ℝ,
        ContinuousOn (fun r : ℝ =>
          shootingCoordinates μ ((φ (-T r) (S r) : LeftEnergyState μ c) : Phase)) (Set.Ioo 0 b) ∧
        Filter.Tendsto (fun r : ℝ =>
          shootingCoordinates μ ((φ (-T r) (S r) : LeftEnergyState μ c) : Phase))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.sqrt 2 / 2, 0)) ∧
        Filter.Tendsto (fun r : ℝ =>
          shootingCoordinates μ ((φ (-T r) (S r) : LeftEnergyState μ c) : Phase))
          (nhdsWithin b (Set.Iio b)) (nhds (α, 0)) ∧
        ∀ r ∈ Set.Ioo 0 b,
          ((S r : LeftEnergyState μ c) : Phase) 1 = 0 ∧
          ((S r : LeftEnergyState μ c) : Phase) 2 = 0 ∧
          ((S r : LeftEnergyState μ c) : Phase) 0 ≠ 0 ∧
          0 < T r ∧
          (∀ t ∈ Set.Ioo (-T r) 0,
            0 < relativePosition μ ((φ t (S r) : LeftEnergyState μ c) : Phase) 0 ∧
            relativePosition μ ((φ t (S r) : LeftEnergyState μ c) : Phase) 1 < 0) ∧
          relativePosition μ ((φ (-T r) (S r) : LeftEnergyState μ c) : Phase) 1 < 0 ∧
          relativePosition μ ((φ (-T r) (S r) : LeftEnergyState μ c) : Phase) 0 = 0 := by sorry

end BirkhoffGlobalSection
