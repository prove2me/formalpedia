-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_existsUnique_germToFunctionField_eq_of_iSup_eq
-- name    : AlgebraicGeometry.Scheme.existsUnique_germToFunctionField_eq_of_iSup_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/a33f05d7-1028-51f5-b2e0-461ad4325836
-- title:
--   Regular functions glue inside the function field
-- statement:
--   Let $X$ be an integral scheme, let $\iota$ be an index type in the same universe, let $V : \iota \to$ `X.Opens` be a family of open subsets of $X$ and let $W$ be an open subset of $X$ with $\bigvee_i V_i = W$; assume $W$ is nonempty and each $V_i$ is nonempty. Let $f$ be an element of the function field `X.functionField` of $X$, that is, of the stalk of $\mathcal{O}_X$ at the generic point, and let $s$ assign to each $i$ a section $s_i \in \Gamma(X, V_i)$ such that the germ map `X.germToFunctionField (V i)` carries $s_i$ to $f$ for every $i$. The assertion is that there exists exactly one section $t \in \Gamma(X, W)$ satisfying both: the germ of $t$ at the generic point equals $f$, and for every $i$ the restriction of $t$ along the inclusion $V_i \le W$ (obtained from $\bigvee_i V_i = W$) equals $s_i$. Thus $\Gamma(X,W)$ is the intersection of the $\Gamma(X,V_i)$ inside the function field, in the strong form that the intersecting element is realised by a single section.
--
--   This is the standard statement that on an integral scheme a rational function which is regular on each member of an open cover of $W$ is regular on $W$, the gluing being automatic because all restriction maps and all maps $\Gamma(X,U) \to K(X)$ with $U$ nonempty are injective. It is used in the construction of the norm of a regular function along a finite morphism onto a normally integrally closed base, in [`AlgebraicGeometry.Scheme.exists_normSections_mul_map_eq_norm_of_isFinite_of_isIntegrallyClosed`](thm.html#AlgebraicGeometry.Scheme.exists_normSections_mul_map_eq_norm_of_isFinite_of_isIntegrallyClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_existsUnique_germToFunctionField_eq_of_iSup_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

theorem AlgebraicGeometry.Scheme.existsUnique_germToFunctionField_eq_of_iSup_eq
    {X : Scheme.{u}} [IsIntegral X] {ι : Type u} (V : ι → X.Opens) (W : X.Opens) (hV : iSup V = W)
    [hW : Nonempty W] [hVi : ∀ i, Nonempty (V i)]
    (f : X.functionField) (s : ∀ i, Γ(X, V i)) (hs : ∀ i, X.germToFunctionField (V i) (s i) = f) :
    ∃! t : Γ(X, W), X.germToFunctionField W t = f ∧
      ∀ i, X.presheaf.map (homOfLE (hV ▸ le_iSup V i : V i ≤ W)).op t = s i := by sorry
