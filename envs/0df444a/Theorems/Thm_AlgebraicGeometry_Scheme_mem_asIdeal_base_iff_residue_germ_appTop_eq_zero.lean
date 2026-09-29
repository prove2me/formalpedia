-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_mem_asIdeal_base_iff_residue_germ_appTop_eq_zero
-- name    : AlgebraicGeometry.Scheme.mem_asIdeal_base_iff_residue_germ_appTop_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/b5c8dced-ddd5-59b3-91af-475b4a8dcddd
-- title:
--   Membership in the image prime versus vanishing of the pulled-back function
-- statement:
--   Let $X$ be a scheme, $R$ a commutative ring, $f\colon X\to\operatorname{Spec} R$ a morphism of schemes, $y$ a point of $X$, and $c$ an element of $R$. The assertion is an equivalence between two conditions. On one side, $c$ belongs to the prime ideal of $R$ corresponding to the image point $f(y)$ of the underlying topological space map of $f$. On the other side, consider the global section of $\mathcal O_X$ obtained from $c$ by first transporting $c$ through the inverse of the canonical isomorphism $\Gamma(\operatorname{Spec} R,\mathcal O_{\operatorname{Spec} R})\cong R$ and then applying the map on global sections induced by $f$; take its germ at $y$ in the stalk $\mathcal O_{X,y}$, and then its image under the residue map of the local ring $\mathcal O_{X,y}$ onto its residue field. The condition is that this residue is zero, i.e. that the germ at $y$ lies in the maximal ideal of $\mathcal O_{X,y}$. Thus $c\in f(y)$ if and only if the pull-back $f^{*}c$ vanishes at $y$ in the residue field $\kappa(y)$.
--
--   This is the standard description of the image point of a morphism to an affine scheme as the ideal of functions from the base vanishing at the given point, equivalently the statement that $y$ lies over the basic open $D(c)$ exactly when $f^{*}c$ does not vanish at $y$. It is used on the level-$\Gamma_H$ Deligne–Rapoport models to recognise, for a point of the model over a base ring, whether a given element of the base (typically a uniformiser) vanishes there, hence whether the point lies in the generic fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_mem_asIdeal_base_iff_residue_germ_appTop_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.mem_asIdeal_base_iff_residue_germ_appTop_eq_zero
    {X : Scheme.{u}} {R : CommRingCat.{u}} (f : X ⟶ Spec R) (y : X) (c : R) :
    c ∈ (f.base y).asIdeal ↔
      X.residue y ((X.presheaf.germ ⊤ y trivial) (f.appTop ((Scheme.ΓSpecIso R).inv c))) = 0 := by sorry
