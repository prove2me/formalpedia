-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_ball_radial_convexity
-- name    : BirkhoffGlobalSection.inner_lagrange_ball_radial_convexity
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T21:26:18.824307+00:00
-- url     : https://prove2.me/theorems/dc3b716a-3d0d-4740-b0cc-16f721f5ffdd
-- title:
--   Radial convexity of the effective potential inside the first Lagrange ball
-- statement:
--   This is the uniform radial convexity of the effective potential inside the ball reaching the first Lagrange point.
--
--   Fix a mass ratio $0<\mu<1$ in the planar circular restricted three-body problem, with the primary of mass $1-\mu$ at $(-\mu,0)$ and the primary of mass $\mu$ at $(1-\mu,0)$. Use polar coordinates $(\rho,\theta)$ centred at the first primary and write $\kappa=\cos\theta\in[-1,1]$. The effective potential (with the sign convention in which the Jacobi Hamiltonian is $\tfrac12|p+Jq|^2-\Omega(q)$) is
--   $$
--   \Omega(\rho,\kappa)=\frac{\rho^2-2\mu\rho\kappa+\mu^2}{2}+\frac{1-\mu}{\rho}+\frac{\mu}{\sqrt{\rho^2-2\rho\kappa+1}},
--   $$
--   where $\sqrt{\rho^2-2\rho\kappa+1}$ is the distance to the second primary. Let $L$ be the inner collinear Lagrange point, the equilibrium strictly between the two primaries, and let $d=L_1+\mu\in(0,1)$ be its distance from the first primary.
--
--   For every $0<\rho\le d$ and every $\kappa\in[-1,1]$,
--   $$
--   \frac{\partial^2\Omega}{\partial\rho^2}(\rho,\kappa)=1+\frac{2(1-\mu)}{\rho^3}+\frac{\mu\bigl(3(\rho-\kappa)^2-(\rho^2-2\rho\kappa+1)\bigr)}{(\rho^2-2\rho\kappa+1)^{5/2}}\ \ge\ 1 .
--   $$
--
--   The second radial derivative of the effective potential is therefore at least that of the centrifugal term $\tfrac12\rho^2$ throughout the closed ball of radius $d$ about the first primary, with the primary removed. Combined with radial monotonicity, it yields the key estimate for the transversality of the Liouville vector field to the subcritical energy hypersurface.
--
--   **Formalization Note** The statement is written with the explicit formula for the second radial derivative. Up to the relabelling $\mu\leftrightarrow1-\mu$ and $\Omega=-U$, this is the source's Lemma 5.5.
-- source:
--   Albers--Frauenfelder--van Koert--Paternain, Contact geometry of the restricted three-body problem, Comm. Pure Appl. Math. 65 (2012), https://arxiv.org/abs/1010.2140, Section 5, Lemma 5.5 (stated there for the moon's lunar polar coordinates; here with the mass labels swapped, mu <-> 1-mu). Used for the star-shapedness in Joung--van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 2.4.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem inner_lagrange_ball_radial_convexity (μ : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (L : Phase) (hL : IsInnerLagrangePoint μ L)
    (ρ κ : ℝ) (hρ0 : 0 < ρ) (hρd : ρ ≤ L 0 + μ)
    (hκ0 : -1 ≤ κ) (hκ1 : κ ≤ 1) :
    1 ≤ 1 + 2 * (1 - μ) / ρ ^ 3 +
      μ * (3 * (ρ - κ) ^ 2 - (ρ ^ 2 - 2 * ρ * κ + 1)) /
        Real.sqrt (ρ ^ 2 - 2 * ρ * κ + 1) ^ 5 := by sorry

end BirkhoffGlobalSection
