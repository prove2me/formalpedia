-- Prove2me | Theorems.Thm_AlgebraicGeometry_tilde_pullbackSpecIso_unit
-- name    : AlgebraicGeometry.tilde.pullbackSpecIso_unit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/6043f099-b385-5b84-bc01-314f21576080
-- title:
--   Base-change isomorphism for ·̃ respects adjunction units
-- statement:
--   Let $R$ and $S$ be commutative rings (objects of `CommRingCat`), let $\varphi\colon R\to S$ be a ring homomorphism and let $M$ be an $R$-module. Write $f=\operatorname{Spec}\varphi$ for the induced morphism of affine schemes, and $\beta_M$ for the component `tilde.pullbackSpecIso φ M` at $M$ of the isomorphism of functors `tilde.functorCompPullbackSpecIso φ`, i.e. the isomorphism $f^{*}\widetilde M\cong\widetilde{S\otimes_R M}$ obtained by applying uniqueness of left adjoints (`Adjunction.leftAdjointUniq`) to the composite adjunction $\widetilde{\;\cdot\;}\dashv\Gamma$ followed by $f^{*}\dashv f_{*}$, and to the composite of extension of scalars $\dashv$ restriction of scalars with $\widetilde{\;\cdot\;}\dashv\Gamma$ over $S$, the latter transported along the natural isomorphism `Scheme.Modules.pushforwardSpecCompΓIso φ` identifying $f_{*}$ followed by global sections over $\operatorname{Spec} R$ with global sections over $\operatorname{Spec} S$ viewed by restriction of scalars. The assertion is an equality of morphisms of $R$-modules out of $M$: the unit at $M$ of the composite adjunction $(\widetilde{\;\cdot\;}\dashv\Gamma)\circ(f^{*}\dashv f_{*})$, followed by the image of $\beta_M$ under $f_{*}$ composed with the global-sections functor `moduleSpecΓFunctor` over $R$, followed by the component of `Scheme.Modules.pushforwardSpecCompΓIso φ` at $\widetilde{S\otimes_R M}$, equals the unit $M\to S\otimes_R M$ of extension–restriction of scalars followed by the restriction of scalars along $\varphi$ of the unit at $S\otimes_R M$ of the adjunction $\widetilde{\;\cdot\;}\dashv\Gamma$ over $S$.
--
--   This is the normalisation property pinning down the classical base-change isomorphism $f^{*}\widetilde M\cong\widetilde{S\otimes_R M}$ for quasi-coherent modules on affine schemes: on global sections it is the map induced by $m\mapsto 1\otimes m$, a condition that naturality in $M$ alone does not determine. It is used in the identification of base-change comparison maps on sections, being cited by [`AlgebraicGeometry.Scheme.Modules.isIso_baseChange_sections_of_isIso_fromTildeGamma`](thm.html#AlgebraicGeometry.Scheme.Modules.isIso_baseChange_sections_of_isIso_fromTildeGamma) and by the compatibility of `tilde.pullbackSpecIso` with composition of pullbacks.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_tilde_pullbackSpecIso_unit.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesTildePullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Opposite TensorProduct

theorem AlgebraicGeometry.tilde.pullbackSpecIso_unit {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (M : ModuleCat.{u} R) :
    ((tilde.adjunction (R := R)).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).unit.app M ≫
      (Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R)).map
        (tilde.pullbackSpecIso φ M).hom ≫
      (Scheme.Modules.pushforwardSpecCompΓIso φ).hom.app
        (tilde ((ModuleCat.extendScalars φ.hom).obj M)) =
    (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M ≫
      (ModuleCat.restrictScalars φ.hom).map
        ((tilde.adjunction (R := S)).unit.app ((ModuleCat.extendScalars φ.hom).obj M)) := by sorry
