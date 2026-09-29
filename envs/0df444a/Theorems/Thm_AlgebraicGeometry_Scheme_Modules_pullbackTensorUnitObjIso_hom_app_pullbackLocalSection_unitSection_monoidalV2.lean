-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection_monoidalV2
-- name    : AlgebraicGeometry.Scheme.Modules.pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/72faad68-3738-51bc-b51e-4113d392a32e
-- title:
--   Pullback of the unit section is the unit section
-- statement:
--   Let $X$ and $Y$ be schemes (in a fixed universe), let $\varphi \colon X \to Y$ be a morphism of schemes and let $U$ be an open subset of $Y$. Consider the inverse-image functor `Modules.pullback` $\varphi$ on sheaves of modules, and the isomorphism `pullbackTensorUnitObjIso` $\varphi$, defined as the inverse of the monoidal unit comparison `Functor.Monoidal.εIso` of that functor, so an isomorphism $\varphi^{*}(\mathbb{1}_{Y.\mathrm{Modules}}) \cong \mathbb{1}_{X.\mathrm{Modules}}$ of sheaves of modules on $X$. Take the unit section `unitSection` $U$, that is the element $1$ of $\Gamma(Y, U)$ viewed as a section of the monoidal unit over $U$, and form `pullbackLocalSection` $\varphi$ of it, namely its image under the component at $U$ of the morphism of sheaves obtained by evaluating the unit of the adjunction `Modules.pullbackPushforwardAdjunction` $\varphi$ at the monoidal unit; this is a section of $\varphi^{*}(\mathbb{1}_{Y.\mathrm{Modules}})$ over $\varphi^{-1}U$. The assertion is that applying the component at $\varphi^{-1}U$ of the forward direction of `pullbackTensorUnitObjIso` $\varphi$ to this section yields `unitSection` $(\varphi^{-1}U)$, the element $1$ of $\Gamma(X, \varphi^{-1}U)$.
--
--   This is the compatibility of the monoidal structure on inverse image of sheaves of modules with unit sections: the pulled-back unit section of $\mathcal{O}_Y$ is identified with the unit section of $\mathcal{O}_X$ over the preimage open. It is used in the treatment of pullbacks of tensor powers and of framings, being cited by [`AlgebraicGeometry.Scheme.Modules.IsFrameOn.pullbackLocalSection_monoidalV2`](thm.html#AlgebraicGeometry.Scheme.Modules.IsFrameOn.pullbackLocalSection_monoidalV2), [`AlgebraicGeometry.Scheme.Modules.app_pullbackTensorPowIso_tensorPowMapIso_unitSection`](thm.html#AlgebraicGeometry.Scheme.Modules.app_pullbackTensorPowIso_tensorPowMapIso_unitSection) and [`AlgebraicGeometry.Scheme.Modules.pullbackTensorUnitObjIso_eq_pullbackUnitIso`](thm.html#AlgebraicGeometry.Scheme.Modules.pullbackTensorUnitObjIso_eq_pullbackUnitIso).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection_monoidalV2.lean

import Mathlib
import Definitions.Def_PresheafOfModules_InternalHom
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_PresheafOfModules_PullbackMonoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.Modules.pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection_monoidalV2
    {X Y : AlgebraicGeometry.Scheme.{u}} (φ : X ⟶ Y) (U : Y.Opens) :
    (AlgebraicGeometry.Scheme.Modules.pullbackTensorUnitObjIso φ).hom.app (φ ⁻¹ᵁ U)
      (AlgebraicGeometry.Scheme.Modules.pullbackLocalSection φ
        (AlgebraicGeometry.Scheme.Modules.unitSection U)) =
    AlgebraicGeometry.Scheme.Modules.unitSection (φ ⁻¹ᵁ U) := by sorry
