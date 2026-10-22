-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_ball_radial_force_negative
-- name    : BirkhoffGlobalSection.inner_lagrange_ball_radial_force_negative
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T21:26:19.880297+00:00
-- url     : https://prove2.me/theorems/6ee8cc96-37e6-4de3-ab8a-ee556deb6b1c
-- title:
--   Radial monotonicity of the effective potential inside the first Lagrange ball
-- statement:
--   This is the radial monotonicity of the effective potential inside the ball reaching the first Lagrange point.
--
--   Fix a mass ratio $0<\mu<1$ in the planar circular restricted three-body problem, with the primary of mass $1-\mu$ at $(-\mu,0)$ and the primary of mass $\mu$ at $(1-\mu,0)$. Use polar coordinates $(\rho,\theta)$ centred at the first primary and write $\kappa=\cos\theta\in[-1,1]$. The effective potential (with the sign convention in which the Jacobi Hamiltonian is $\tfrac12|p+Jq|^2-\Omega(q)$) is
--   $$
--   \Omega(\rho,\kappa)=\frac{\rho^2-2\mu\rho\kappa+\mu^2}{2}+\frac{1-\mu}{\rho}+\frac{\mu}{\sqrt{\rho^2-2\rho\kappa+1}},
--   $$
--   where $\sqrt{\rho^2-2\rho\kappa+1}$ is the distance to the second primary. Let $L$ be the inner collinear Lagrange point, the equilibrium strictly between the two primaries, and let $d=L_1+\mu\in(0,1)$ be its distance from the first primary.
--
--   For every $0<\rho<d$ and every $\kappa\in[-1,1]$,
--   $$
--   \frac{\partial\Omega}{\partial\rho}(\rho,\kappa)=\rho-\mu\kappa-\frac{1-\mu}{\rho^2}-\frac{\mu(\rho-\kappa)}{(\rho^2-2\rho\kappa+1)^{3/2}}<0 .
--   $$
--
--   In other words, the effective potential strictly decreases along every ray leaving the first primary before the ray reaches the circle through the inner Lagrange point. Together with the radial convexity estimate, this gives the star-shapedness (Liouville transversality) of the subcritical energy hypersurface around that primary.
--
--   **Formalization Note** The statement is written with the explicit formula for the radial derivative. Up to the relabelling $\mu\leftrightarrow1-\mu$ and $\Omega=-U$, this is the source's Lemma 5.4, restricted to the open ball.
-- source:
--   Albers--Frauenfelder--van Koert--Paternain, Contact geometry of the restricted three-body problem, Comm. Pure Appl. Math. 65 (2012), https://arxiv.org/abs/1010.2140, Section 5, Lemma 5.4 (stated there for the moon's lunar polar coordinates; here with the mass labels swapped, mu <-> 1-mu). Used for the star-shapedness in Joung--van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 2.4.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem inner_lagrange_ball_radial_force_negative (μ : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (L : Phase) (hL : IsInnerLagrangePoint μ L)
    (ρ κ : ℝ) (hρ0 : 0 < ρ) (hρd : ρ < L 0 + μ)
    (hκ0 : -1 ≤ κ) (hκ1 : κ ≤ 1) :
    ρ - μ * κ - (1 - μ) / ρ ^ 2 -
      μ * (ρ - κ) / Real.sqrt (ρ ^ 2 - 2 * ρ * κ + 1) ^ 3 < 0 := by sorry

end BirkhoffGlobalSection
