-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_isLocalization_atPrime_stalk_of_specializes
-- name    : AlgebraicGeometry.Scheme.isLocalization_atPrime_stalk_of_specializes
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/9570a42b-95b6-52f3-8927-f055b0a2b692
-- title:
--   Stalk at a generalisation as a localisation of the stalk
-- statement:
--   Let $X$ be a scheme and let $x,y$ be points of its underlying space with $y \rightsquigarrow x$, that is, $x$ lies in the closure of $\{y\}$, so that $y$ is a generalisation of $x$. The specialisation morphism of rings $\mathcal{O}_{X,x} \to \mathcal{O}_{X,y}$ given by `X.presheaf.stalkSpecializes h` is used to regard the stalk at $y$ as an algebra over the stalk at $x$. The assertion is that, with this algebra structure, $\mathcal{O}_{X,y}$ is a localisation of $\mathcal{O}_{X,x}$ at the prime ideal obtained by pulling back the maximal ideal of the local ring $\mathcal{O}_{X,y}$ along that specialisation map, in Mathlib's sense `IsLocalization.AtPrime`: the complement of this pulled-back ideal is sent to units of $\mathcal{O}_{X,y}$, every element of $\mathcal{O}_{X,y}$ has the form (image of $a$) times (image of $s$)$^{-1}$ with $s$ outside the ideal, and two elements of $\mathcal{O}_{X,x}$ with equal images are identified after multiplication by a single element outside the ideal. Thus $\mathcal{O}_{X,y} \cong (\mathcal{O}_{X,x})_{\mathfrak{p}_y}$ with $\mathfrak{p}_y$ the contracted maximal ideal.
--
--   This is the standard local description of specialisation: along $y \rightsquigarrow x$ the local ring at the more generic point $y$ is a localisation of the local ring at $x$, the affine picture being $\mathcal{O}_{\operatorname{Spec} A, \mathfrak{q}} = (A_{\mathfrak{p}})_{\mathfrak{q}A_{\mathfrak{p}}}$ for $\mathfrak{q} \subseteq \mathfrak{p}$. It is used in the component-reading part of the Néron model infrastructure, where germs at a generic point are compared with germs at a special point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_isLocalization_atPrime_stalk_of_specializes.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology

theorem AlgebraicGeometry.Scheme.isLocalization_atPrime_stalk_of_specializes
    {X : Scheme.{u}} {x y : ↥X} (h : y ⤳ x) :
    letI : Algebra ↑(X.presheaf.stalk x) ↑(X.presheaf.stalk y) := (X.presheaf.stalkSpecializes h).hom.toAlgebra
    IsLocalization.AtPrime ↑(X.presheaf.stalk y)
      (Ideal.comap (X.presheaf.stalkSpecializes h).hom (IsLocalRing.maximalIdeal ↑(X.presheaf.stalk y))) := by sorry
