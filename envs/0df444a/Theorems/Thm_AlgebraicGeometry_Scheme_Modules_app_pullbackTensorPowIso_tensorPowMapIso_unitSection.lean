-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_app_pullbackTensorPowIso_tensorPowMapIso_unitSection
-- name    : AlgebraicGeometry.Scheme.Modules.app_pullbackTensorPowIso_tensorPowMapIso_unitSection
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/d2607588-b9d1-5cf1-86a6-ea243763935f
-- title:
--   Unit section preserved by the degree-zero tensor-power comparison
-- statement:
--   Let $X$ and $X'$ be schemes, $c : X' \to X$ a morphism, $L$ an object of $X$'s category of modules, $L'$ an object of $X'$'s, and $e : c^{*}L \cong L'$ an isomorphism, where $c^{*}$ denotes `Scheme.Modules.pullback c`. Consider the degree-zero instances of the two comparison isomorphisms: `Scheme.Modules.pullbackTensorPowIso c L 0` is, by definition, the isomorphism `pullbackTensorUnitObjIso c` : $c^{*}(\mathbf 1) \cong \mathbf 1$ inverse to the monoidal unit constraint of $c^{*}$ (here $\mathbf 1$ is the monoidal unit of the relevant module category, and $L^{\otimes 0} = \mathbf 1$ by the recursive definition of `tensorPow`), and `Scheme.Modules.tensorPowMapIso e 0` is the identity isomorphism of $\mathbf 1$. The assertion is an equality of sections over the top open subset: take `Scheme.Modules.unitSection ⊤`, namely the section $1 \in \Gamma(X, \top)$ viewed as a section of $\mathbf 1$, push it through the component at $\top$ of the unit of the adjunction `pullbackPushforwardAdjunction c` evaluated at $L^{\otimes 0}$, and then apply the component at $\top$ of the composite isomorphism above; the result is again the unit section, i.e. $1 \in \Gamma(X', \top)$.
--
--   This is the degree-zero base case of the compatibility of the canonical isomorphisms $c^{*}(L^{\otimes n}) \cong (c^{*}L)^{\otimes n} \cong L'^{\otimes n}$ with the multiplicative structure on sections: the pull-back of the section $1$ of $L^{\otimes 0} = \mathcal O_X$ is the section $1$ of $\mathcal O_{X'}$. It is used in the construction of algebra homomorphisms between section rings of graded $\mathcal O$-algebras along a pull-back square, in [`AlgebraicGeometry.GradedOAlgebra.IsSectionRing.exists_algHom_apply_eq_pullback_of_isPullback`](thm.html#AlgebraicGeometry.GradedOAlgebra.IsSectionRing.exists_algHom_apply_eq_pullback_of_isPullback).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_app_pullbackTensorPowIso_tensorPowMapIso_unitSection.lean

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraSectionRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

theorem AlgebraicGeometry.Scheme.Modules.app_pullbackTensorPowIso_tensorPowMapIso_unitSection
    {X X' : Scheme.{u}} (c : X' ⟶ X) (L : X.Modules) (L' : X'.Modules) (e : (Scheme.Modules.pullback c).obj L ≅ L') :
    ((Scheme.Modules.pullbackTensorPowIso c L 0 ≪≫ Scheme.Modules.tensorPowMapIso e 0).hom.app ⊤) ((((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app (L.tensorPow 0)).app ⊤) (Scheme.Modules.unitSection ⊤))
      = Scheme.Modules.unitSection ⊤ := by sorry
