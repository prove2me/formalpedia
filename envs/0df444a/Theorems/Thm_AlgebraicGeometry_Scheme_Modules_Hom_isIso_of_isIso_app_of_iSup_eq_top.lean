-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_Hom_isIso_of_isIso_app_of_iSup_eq_top
-- name    : AlgebraicGeometry.Scheme.Modules.Hom.isIso_of_isIso_app_of_iSup_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/ebd2f74f-f9c3-5e96-82bc-e85b2cb71f0b
-- title:
--   Isomorphy of mathcal O_X-module morphisms is local on an open cover
-- statement:
--   Let $X$ be a scheme and let $M, N$ be sheaves of $\mathcal O_X$-modules on $X$ (objects of `X.Modules`), and let $\varphi \colon M \to N$ be a morphism between them. Let $\iota$ be a type, in a universe independent of that of $X$, and let $U \colon \iota \to$ `X.Opens` be a family of open subsets of $X$ whose supremum in the lattice of opens is the whole space, $\bigsqcup_i U_i = \top$. Assume that for every index $i$ and every open $V$ of $X$ with $V \le U_i$ the induced map on sections $\varphi_V \colon M(V) \to N(V)$ is an isomorphism (`IsIso (φ.app V)`). Then $\varphi$ is an isomorphism in the category `X.Modules`, that is, it admits a two-sided inverse morphism of $\mathcal O_X$-modules. Note that the hypothesis is imposed not merely at the members $U_i$ of the cover but at all opens contained in some member of it.
--
--   This is the standard locality of the property of being an isomorphism for morphisms of sheaves of modules on a scheme. It is used in the project to compare invertible sheaves on opens over which they are trivialised, for instance to identify $\mathcal O(-Z_1-Z_2)$ with $\mathcal O(-Z_1)\otimes\mathcal O(-Z_2)$ and $f^*\mathcal O(-Z)$ with $\mathcal O(-f^{-1}Z)$, and is cited by the results on invertible modules and on pullback comparison maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_Hom_isIso_of_isIso_app_of_iSup_eq_top.lean

import Mathlib.AlgebraicGeometry.Modules.Sheaf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.Hom.isIso_of_isIso_app_of_iSup_eq_top
    {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) {ι : Type v}
    (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (h : ∀ (i : ι) (V : X.Opens), V ≤ U i → IsIso (φ.app V)) : IsIso φ := by sorry
