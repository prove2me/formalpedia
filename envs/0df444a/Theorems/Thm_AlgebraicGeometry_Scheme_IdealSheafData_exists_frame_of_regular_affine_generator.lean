-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_exists_frame_of_regular_affine_generator
-- name    : AlgebraicGeometry.Scheme.IdealSheafData.exists_frame_of_regular_affine_generator
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-07T12:40:32.306345+00:00
-- url     : https://prove2.me/theorems/39bc6fe0-39c8-4e99-8e5c-37a7fec47027
-- title:
--   A regular affine ideal generator gives an exact frame of its ideal module
-- statement:
--   Let $X$ be a scheme, let $\mathcal I\subseteq\mathcal O_X$ be a quasi-coherent ideal, and let $W\subseteq X$ be an affine open. Suppose that $g\in\Gamma(W,\mathcal O_X)$ is a non-zero-divisor and generates the ideal $\mathcal I(W)$. Let $M$ be the registered ideal module, defined as the kernel of $\mathcal O_X\to i_*\mathcal O_{V(\mathcal I)}$, with its inclusion $\iota:M\to\mathcal O_X$.
--   There is a section $m\in\Gamma(W,M)$ with $\iota(m)=g$ which freely generates $M$ on every open subset of $W$: for every $T\subseteq W$, the map
--   $$\Gamma(T,\mathcal O_X)\longrightarrow\Gamma(T,M),\qquad a\longmapsto a\,m|_T$$
--   is bijective. No nonemptiness, integrality, reducedness or Noetherian hypothesis is imposed on $X$ or $W$.
--
--   This gives the local trivialization of an effective Cartier ideal with its actual defining equation as the image of the frame. In nodal modifications it identifies sections of a single global ideal module with the coefficient functions used in the local projective embeddings.
-- source:
--   Derived local frame formulation of The Stacks Project, Lemma 31.14.2, tag 01WS, proof of (2) => (1), https://stacks.math.columbia.edu/tag/01WS , together with regularity on all opens as in Section 31.15, Lemma 31.15.7, https://stacks.math.columbia.edu/tag/0C4S . The formal statement uses the registered kernel realization of the ideal module and records the exact image of its frame. This is the local regular-generator argument used in the nodal Cartier-center step for the Philippon alteration frontier; it does not assert the full alteration theorem.

import Mathlib
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
universe u

theorem AlgebraicGeometry.Scheme.IdealSheafData.exists_frame_of_regular_affine_generator
    {X : Scheme.{u}} (I : X.IdealSheafData) (W : X.affineOpens) (g : Γ(X, W))
    (hg : g ∈ nonZeroDivisors Γ(X, W)) (hI : I.ideal W = Ideal.span {g}) :
    ∃ m : Γ(I.module, W), I.moduleι.app W m = g ∧ Scheme.Modules.IsFrameOn m W := by sorry
