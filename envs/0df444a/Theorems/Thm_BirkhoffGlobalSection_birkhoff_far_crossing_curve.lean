-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_birkhoff_far_crossing_curve
-- name    : BirkhoffGlobalSection.birkhoff_far_crossing_curve
-- status  : Open
-- author  : @Mazecto
-- created : 2026-09-25T08:52:04.948043+00:00
-- url     : https://prove2.me/theorems/7b57b9d1-dad6-4dea-90c2-1c84cbd7b1ab
-- title:
--   Birkhoff's far family: continuous crossing curve with collision limits
-- statement:
--   Fix $0<\mu<1$ and a Jacobi energy $-c$ below the first critical value. Let $\Sigma_{\mu,c}$ be the selected Levi-Civita component around the primary $P$ of mass $1-\mu$, with points $s=(z,w)\in\mathbb R^4$. Let $\varphi$ be a continuous flow on $\Sigma_{\mu,c}$ whose time derivative at $t=0$ is the Hamiltonian vector field of the regularized Hamiltonian $K_{\mu,c}$. Write $x(s)=(x_1,x_2)=2z^2$ for the physical position relative to $P$, $v(s)$ for the rotating-frame (Jacobi) velocity, and $(\sigma,\eta)=(v_2/|v|,\,-x_2)$ for Birkhoff's shooting coordinates.
--
--   **Far family as a crossing curve.** There are $b>0$, a point $E$ of the rectangle boundary, states $S(r)$ and times $T(r)$, for $0<r<b$, with the following properties.
--
--   1. Either $E$ lies on a vertical side with positive height ($E_1=\pm1$, $E_2>0$), or it lies on the bottom with $E_1>\sqrt2/2$.
--   2. $S(r)$ starts perpendicularly on the far half-axis: $z_1=w_2=0\ne z_2$.
--   3. $T(r)>0$. On $(0,T(r)]$ the forward trajectory stays strictly below the axis. $t\mapsto x_1(\varphi_t S(r))$ is strictly increasing on $[0,T(r)]$. At $t=T(r)$ the trajectory is on the line $x_1=0$ with $v_1>0$.
--   4. The crossing coordinates
--   $$
--   F(r)=(\sigma,\eta)\bigl(\varphi_{T(r)}S(r)\bigr)
--   $$
--   depend continuously on $r\in(0,b)$, and
--   $$
--   \lim_{r\to0^+}F(r)=\bigl(-\tfrac{\sqrt2}{2},0\bigr),\qquad \lim_{r\to b^-}F(r)=E.
--   $$
--
--   This is the analytic content of Birkhoff's far family $\Gamma_1$, followed until its crossing curve first leaves the open rectangle.
--
--   **Formalization Note** The states $S(r)$ are only required to exist; in Birkhoff's construction $S(r)$ is the perpendicular start at distance $2r^2$ from $P$ on the side away from the second primary.
-- source:
--   Liu--Salomao, Finite energy foliations in the restricted three-body problem, https://arxiv.org/abs/2506.17867v2, Section 5, proof of Theorem 5.1 (pp. 30-31): the curves Gamma_1, Gamma_2 traced by the perpendicular starts; after G. D. Birkhoff, The restricted problem of three bodies, Rend. Circ. Mat. Palermo 39 (1915), Sections 16-18 (Collected Mathematical Papers Vol. 1, pp. 731-741).

import Definitions.Def_BirkhoffShootingCoordinates
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic

namespace BirkhoffGlobalSection

theorem birkhoff_far_crossing_curve (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) :
    ∃ b : ℝ, 0 < b ∧ ∃ E : ℝ × ℝ,
      (((E.1 = -1 ∨ E.1 = 1) ∧ 0 < E.2) ∨ (E.2 = 0 ∧ Real.sqrt 2 / 2 < E.1)) ∧
      ∃ S : ℝ → LeftEnergyState μ c, ∃ T : ℝ → ℝ,
        ContinuousOn (fun r : ℝ =>
          shootingCoordinates μ ((φ (T r) (S r) : LeftEnergyState μ c) : Phase)) (Set.Ioo 0 b) ∧
        Filter.Tendsto (fun r : ℝ =>
          shootingCoordinates μ ((φ (T r) (S r) : LeftEnergyState μ c) : Phase))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (-(Real.sqrt 2 / 2), 0)) ∧
        Filter.Tendsto (fun r : ℝ =>
          shootingCoordinates μ ((φ (T r) (S r) : LeftEnergyState μ c) : Phase))
          (nhdsWithin b (Set.Iio b)) (nhds E) ∧
        ∀ r ∈ Set.Ioo 0 b,
          ((S r : LeftEnergyState μ c) : Phase) 0 = 0 ∧
          ((S r : LeftEnergyState μ c) : Phase) 3 = 0 ∧
          ((S r : LeftEnergyState μ c) : Phase) 1 ≠ 0 ∧
          0 < T r ∧
          (∀ u ∈ Set.Ioo 0 (T r),
            relativePosition μ ((φ u (S r) : LeftEnergyState μ c) : Phase) 1 < 0) ∧
          relativePosition μ ((φ (T r) (S r) : LeftEnergyState μ c) : Phase) 1 < 0 ∧
          StrictMonoOn
            (fun u : ℝ => relativePosition μ ((φ u (S r) : LeftEnergyState μ c) : Phase) 0)
            (Set.Icc 0 (T r)) ∧
          relativePosition μ ((φ (T r) (S r) : LeftEnergyState μ c) : Phase) 0 = 0 ∧
          0 < jacobiVelocity
            (leviCivitaToJacobi μ ((φ (T r) (S r) : LeftEnergyState μ c) : Phase)) 0 := by sorry

end BirkhoffGlobalSection
