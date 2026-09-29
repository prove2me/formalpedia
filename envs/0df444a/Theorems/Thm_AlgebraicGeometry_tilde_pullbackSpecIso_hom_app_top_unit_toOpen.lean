-- Prove2me | Theorems.Thm_AlgebraicGeometry_tilde_pullbackSpecIso_hom_app_top_unit_toOpen
-- name    : AlgebraicGeometry.tilde.pullbackSpecIso_hom_app_top_unit_toOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/015e4780-4801-5fad-a409-3eb9095d900f
-- title:
--   Base-change isomorphism on global sections sends m to 1⊗ m
-- statement:
--   Let $R$ and $S$ be commutative rings (objects of `CommRingCat` in universe $u$), let $\varphi\colon R\to S$ be a ring homomorphism, let $M$ be an $R$-module and let $m\in M$. Write $f=\operatorname{Spec}\varphi\colon\operatorname{Spec}S\to\operatorname{Spec}R$, and let $\beta_M=$ `tilde.pullbackSpecIso φ M` be the component at $M$ of the natural isomorphism $\widetilde{(-)}\circ f^{*}\cong (S\otimes_R-)\circ\widetilde{(-)}$ obtained by uniqueness of left adjoints from, on the one side, the composite of the adjunction $\widetilde{(-)}\dashv\Gamma$ over $R$ with the adjunction $f^{*}\dashv f_{*}$, and, on the other, the composite of extension $\dashv$ restriction of scalars along $\varphi$ with $\widetilde{(-)}\dashv\Gamma$ over $S$, the latter transported along the isomorphism identifying $\Gamma\circ f_{*}$ with restriction of scalars composed with $\Gamma$ over $S$. The assertion is an identity of global sections on $\operatorname{Spec}S$: the image of $m$ under the canonical map $M\to\Gamma(\operatorname{Spec}R,\widetilde M)$, followed by the $\top$-component of the unit of $f^{*}\dashv f_{*}$ at $\widetilde M$ and then by the $\top$-component of $\beta_M$, equals the image of $1\otimes m\in S\otimes_RM$ under the canonical map $S\otimes_RM\to\Gamma(\operatorname{Spec}S,\widetilde{S\otimes_RM})$.
--
--   This is the element-level normalisation of the base-change isomorphism $f^{*}\widetilde M\cong\widetilde{S\otimes_RM}$ for $f=\operatorname{Spec}\varphi$, pinning it down by its effect on global sections. It is used in the comparison of pullbacks of quasi-coherent modules with tensor products over affine opens, feeding the criteria for the base-change morphism of module sheaves to be an isomorphism (for affine morphisms, and over a two-fold affine open cover) and the local description of sections of invertible modules over such covers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_tilde_pullbackSpecIso_hom_app_top_unit_toOpen.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesTildePullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Opposite TensorProduct

theorem AlgebraicGeometry.tilde.pullbackSpecIso_hom_app_top_unit_toOpen {R S : CommRingCat.{u}}
    (φ : R ⟶ S) (M : ModuleCat.{u} R) (m : M) :
    ((tilde.pullbackSpecIso φ M).hom.app ⊤).hom
      ((((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app (tilde M)).app ⊤).hom
        ((tilde.toOpen M ⊤).hom m)) =
    (tilde.toOpen ((ModuleCat.extendScalars φ.hom).obj M) ⊤).hom ((1 : S) ⊗ₜ m) := by sorry
