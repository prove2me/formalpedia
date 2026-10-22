-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_eh_half_mass_star_shaped
-- name    : BirkhoffGlobalSection.eh_half_mass_star_shaped
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-02T12:42:38.270757+00:00
-- url     : https://prove2.me/theorems/7469076e-42a6-4300-8f7d-3b54e886d322
-- title:
--   Equal-mass EH zero level is star-shaped in the left Hill box
-- statement:
--   Fix equal masses $\mu=\tfrac12$ and an energy $c>2$ (physical energy $h=-c$ below the first critical value $-2$). Let $G_c$ be the centered-left elliptic-hyperbolic Hamiltonian `ehLeftHamiltonian (1/2) c` in coordinates $s=(x_1,x_2,y_1,y_2)$. If
--
--   $$G_c(s)=0,\qquad |x_2|\le\frac{\pi}{2},\qquad \cosh^2x_1\le 2c,$$
--
--   then the radial derivative is positive:
--
--   $$dG_c(s)\,s>0 .$$
--
--   At $\mu=\tfrac12$, $G_c=\tfrac12|y+F(x)|^2+V(x)$ with magnetic term $F=\tfrac18(\sin2x_2,\sinh2x_1)$ and decoupled potential $V$. Writing $y_F=y+F$ and $r^2=|y_F|^2=-2V$, the radial derivative is
--
--   $$dG_c(s)\,s=r^2+y_F\cdot\bigl(x_1\partial_1F+x_2\partial_2F-F\bigr)+x\cdot\nabla V .$$
--
--   The box is the left Hill box. $V>0$ on its faces $\cosh^2x_1=2c$ and $|x_2|=\pi/2$, so its zero level is the selected component around the left primary.
--
--   Numerically the minimum is about $0.0115$ at $c=2.0001$, at least $0.3$ for $c\ge2.1$, and it tends to $1$ as $c\to\infty$. It degenerates only in the limit $c\to2$, at the collinear saddle $(x_1,x_2)=(0,\pi/2)$, where the linear term $x_2\,\partial_2V$ still dominates.
--
--   This is the star-shapedness input of the local subcritical convexity branch. With `eh_half_mass_tangential_hessian` and the published perturbation module `BirkhoffGlobalSection_EHConvexPerturbation`, it gives `eh_left_component_regular_compact_starshaped` and `eh_left_component_radial_graph`. Those two leaves need it at every $c_0>2$, for $(\mu,c)$ near $(1/2,c_0)$.
-- source:
--   Liu--Salomao, Finite energy foliations and global dynamics in the restricted three-body problem, https://arxiv.org/html/2506.17867v2#S9.SS3, Theorem 9.4(ii) with the criterion of Theorem 9.1 (positive tangential Hessian iff det U_W > 0) and the monotonicity argument of Lemmas 9.6-9.7; equal masses, energies h = -c < -2. Star-shapedness (positive radial derivative) of the regularized component, implicit in the strict convexity of Theorem 1.12 with the origin inside.

import Definitions.Def_BirkhoffGlobalSection_EHSubcritical

namespace BirkhoffGlobalSection

/-- Equal masses, every subcritical energy `c > 2`: on the zero level of the
centered-left EH Hamiltonian inside the left Hill box `|x₂| ≤ π/2`,
`cosh² x₁ ≤ 2c`, the radial derivative is positive. -/
theorem eh_half_mass_star_shaped (c : ℝ) (hc : 2 < c) (s : Phase)
    (hs : ehLeftHamiltonian (1 / 2) c s = 0)
    (h1 : |s 1| ≤ Real.pi / 2) (h0 : Real.cosh (s 0) ^ 2 ≤ 2 * c) :
    0 < fderiv ℝ (ehLeftHamiltonian (1 / 2) c) s s := by sorry

end BirkhoffGlobalSection
