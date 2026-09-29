-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection
-- name    : AlgebraicGeometry.Scheme.Modules.pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/0968efbb-2809-5320-adbb-84310d237c88
-- title:
--   Pull-back of the unit section is the unit section
-- statement:
--   Let $\varphi\colon X\to Y$ be a morphism of schemes (in a fixed universe) and let $U$ be an open subset of $Y$. On the category $Y.\mathrm{Modules}$ of sheaves of modules over $Y$, the monoidal unit is the structure sheaf, and `unitSection U` denotes the section $1\in\Gamma(Y,U)$ regarded as a section of $\mathbb 1_{Y.\mathrm{Modules}}$ over $U$. The map `pullbackLocalSection` $\varphi$ sends a section of a sheaf of modules $L$ over $U$ to its image under the component at $U$ of the unit of the adjunction between inverse image and direct image along $\varphi$, a section of $(\mathrm{Modules.pullback}\,\varphi).obj\,L$ over $\varphi^{-1}U$. Finally `pullbackTensorUnitObjIso` $\varphi$ is the inverse of the unit comparison isomorphism $\varepsilon$ of the monoidal functor $\mathrm{Modules.pullback}\,\varphi$, hence an isomorphism $(\mathrm{Modules.pullback}\,\varphi).obj\,\mathbb 1_{Y.\mathrm{Modules}}\cong \mathbb 1_{X.\mathrm{Modules}}$. The assertion is that the component of this isomorphism at the open set $\varphi^{-1}U$ carries the pull-back of the unit section of $U$ to the unit section of $\varphi^{-1}U$, i.e. to $1\in\Gamma(X,\varphi^{-1}U)$.
--
--   This records the compatibility of the monoidal structure on the inverse-image functor for sheaves of modules with the distinguished unit sections: the canonical identification $\varphi^{*}\mathcal O_Y\cong\mathcal O_X$ matches $\varphi^{*}(1)$ with $1$. It is used in the treatment of invertible ideal sheaves and of the relative Picard group, for instance in the construction of short exact sequences attached to invertible ideal sheaf data and in the analysis of node unit modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection.lean

import Mathlib
import Definitions.Def_PresheafOfModules_InternalHom
import Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_PresheafOfModules_PullbackMonoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.Modules.pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection
    {X Y : AlgebraicGeometry.Scheme.{u}} (φ : X ⟶ Y) (U : Y.Opens) :
    (AlgebraicGeometry.Scheme.Modules.pullbackTensorUnitObjIso φ).hom.app (φ ⁻¹ᵁ U)
      (AlgebraicGeometry.Scheme.Modules.pullbackLocalSection φ
        (AlgebraicGeometry.Scheme.Modules.unitSection U)) =
    AlgebraicGeometry.Scheme.Modules.unitSection (φ ⁻¹ᵁ U) := by sorry
