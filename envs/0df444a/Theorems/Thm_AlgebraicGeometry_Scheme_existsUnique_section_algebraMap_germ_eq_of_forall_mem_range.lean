-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_existsUnique_section_algebraMap_germ_eq_of_forall_mem_range
-- name    : AlgebraicGeometry.Scheme.existsUnique_section_algebraMap_germ_eq_of_forall_mem_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/ebc8f95d-ac12-5f77-81a7-ebfe9d03d742
-- title:
--   Sections over an open as rational functions regular there
-- statement:
--   Let $X$ be an integral scheme (in the sense of Mathlib's `IsIntegral`, so that $X$ has a generic point and a function field $K(X) = \mathcal{O}_{X,\eta}$, with each stalk $\mathcal{O}_{X,x}$ an algebra over which $K(X)$ is obtained via the specialisation map from $x$ to the generic point), let $W$ be an open subset of $X$, and let $s \in K(X)$. Assume that for every point $x \in W$ the element $s$ lies in the range of the structure map $\mathcal{O}_{X,x} \to K(X)$, i.e. $s$ is the image of some germ at $x$. Then there exists a unique section $u \in \Gamma(X, W)$ such that for every $x \in X$ and every proof that $x \in W$, the image in $K(X)$ of the germ of $u$ at $x$ equals $s$. Uniqueness is asserted in the strong form of `∃!`, i.e. any section with this property coincides with $u$; in particular when $W$ has no points the condition is vacuous and the statement says that $\Gamma(X, W)$ has exactly one element.
--
--   This is the usual identification, for an integral scheme, of $\Gamma(X, W)$ with the intersection $\bigcap_{x \in W} \mathcal{O}_{X,x}$ taken inside the function field: a rational function regular at every point of $W$ comes from a unique section over $W$. It is used to convert stalkwise regularity data into honest sections, and is cited in the construction of morphisms of curve models, via [`AlgebraicCurve.CurveModel.exists_opens_hom_comp_eq_of_existsUnique_evalAt_eq_appLE`](thm.html#AlgebraicCurve.CurveModel.exists_opens_hom_comp_eq_of_existsUnique_evalAt_eq_appLE).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_existsUnique_section_algebraMap_germ_eq_of_forall_mem_range.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

theorem AlgebraicGeometry.Scheme.existsUnique_section_algebraMap_germ_eq_of_forall_mem_range
    {X : Scheme.{u}} [IsIntegral X] (W : X.Opens) (s : X.functionField)
    (hs : ∀ x ∈ W, s ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range) :
    ∃! u : Γ(X, W), ∀ (x : X) (hx : x ∈ W),
      algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ W x hx u) = s := by sorry
