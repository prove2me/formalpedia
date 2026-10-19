-- Prove2me | Theorems.Thm_FlatlyFoliated_asymptotic_helmholtz_potential
-- name    : FlatlyFoliated.asymptotic_helmholtz_potential
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-17T18:27:23.39245+00:00
-- url     : https://prove2.me/theorems/60287910-cad4-4937-abd3-a12c9fbbadc4
-- title:
--   A Poisson potential with decaying remainder for exterior radial vector fields
-- statement:
--   Let $w$ be a smooth vector field on $\mathbb R^3$ which is equivariant under every orthogonal transformation outside some ball centered at the origin. Then there is a smooth scalar potential $f$ satisfying
--   $$\Delta f=\nabla\!\cdot w,\qquad w-\nabla f\longrightarrow0\quad\text{as }|x|\to\infty.$$
--   Writing $\bar f$ for the spherical average of $f$, the difference $g=f-\bar f$ is bounded and satisfies
--   $$\forall\varepsilon>0\;\exists R\;\forall |x|\ge R:\quad |x|^2\|D^2g(x)\|\,\|Dg(x)\|\le\varepsilon.$$
--   This is the potential construction used to pass from the original FFR variables to the elliptic variables in Corollary 2. It depends only on smoothness and exterior spherical symmetry of the vector field; it has no vacuum-equation, cosmological-constant, or lapse hypothesis.
-- source:
--   Bray, Hamm, Hirsch, Wheeler, Zhang, Flatly Foliated Relativity, arXiv:1911.00967v2, https://arxiv.org/abs/1911.00967, Section 5, proof of Corollary 2, decomposition w=w_SS+w_C and Poisson potential preceding eq. (101), decay eqs. (101)–(102), and approximate spherical symmetry after eq. (102). The derivative-norm formulation follows from the compactly supported Poisson correction and its differentiated Newtonian-kernel decay.

import Definitions.Def_FlatlyFoliatedRelativity_basic

open scoped ContDiff Topology
open FlatlyFoliated Filter

theorem FlatlyFoliated.asymptotic_helmholtz_potential
    (w : R3 → R3) (hw : ContDiff ℝ ∞ w)
    (hs : ∃ R : ℝ, 0 < R ∧ ∀ (T : R3 ≃ₗᵢ[ℝ] R3) (x : R3),
      R ≤ ‖x‖ → w (T x) = T (w x)) :
    ∃ f : R3 → ℝ, ContDiff ℝ ∞ f ∧ (∀ x, lap f x = divg w x) ∧
      ApproxSphSymmAtInfty f ∧
      Tendsto (fun x => w x - grad f x) (Bornology.cobounded R3) (𝓝 0) := by sorry
