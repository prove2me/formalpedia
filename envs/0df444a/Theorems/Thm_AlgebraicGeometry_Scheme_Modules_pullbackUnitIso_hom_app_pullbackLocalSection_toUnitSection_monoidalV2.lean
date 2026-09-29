-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection_monoidalV2
-- name    : AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/48bb6878-f586-59e6-8942-33a6c4189151
-- title:
--   Pullback of a function under the trivialisation φ^*mathcal O_Y≅mathcal O_X
-- statement:
--   Let $X$ and $Y$ be schemes, $\varphi : X \to Y$ a morphism, $U$ an open subscheme of $Y$ and $g \in \Gamma(Y, U)$ a section of the structure sheaf of $Y$ over $U$. Write $\mathrm{toUnitSection}\ U\ g$ for $g$ regarded, by definition as the same element, as a section over $U$ of the unit object $\mathbf 1$ of the monoidal category of $\mathcal O_Y$-modules on $Y$, and write $\mathrm{pullbackLocalSection}\ \varphi$ for the map on local sections given by evaluating at $U$ the component at the module in question of the unit of the pullback–pushforward adjunction `Scheme.Modules.pullbackPushforwardAdjunction φ`, landing in sections of the pullback module over $\varphi^{-1}U$. Let `Scheme.Modules.pullbackUnitIso φ` be the isomorphism $\varphi^*\mathbf 1_Y \cong \mathbf 1_X$ obtained from the canonical morphism `SheafOfModules.pullbackObjUnitToUnit` for the induced map of sheaves of rings, which is an isomorphism. The assertion is that the $\varphi^{-1}U$-component of this isomorphism carries the pulled-back section of $g$ to $\mathrm{toUnitSection}\ (\varphi^{-1}U)\ (\varphi^\sharp g)$, where $\varphi^\sharp g =$ `φ.app U g` is the image of $g$ under the map on structure sheaves.
--
--   This is the compatibility of the canonical trivialisation $\varphi^*\mathcal O_Y \cong \mathcal O_X$ with the pullback of sections: it identifies the pulled-back section of a function with the function's image under the morphism of structure sheaves. It is used in the computations with sections of pulled-back invertible modules, for instance in identifying `pullbackTensorUnitObjIso` with `pullbackUnitIso`, in the vanishing criterion for pulled-back sections of a projective presentation, and in the base-change criterion for polarisations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection_monoidalV2.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection_monoidalV2
    {X Y : Scheme.{u}} (φ : X ⟶ Y) (U : Y.Opens) (g : Γ(Y, U)) :
    (Scheme.Modules.pullbackUnitIso φ).hom.app (φ ⁻¹ᵁ U)
        (Scheme.Modules.pullbackLocalSection φ (Scheme.Modules.toUnitSection U g)) =
      Scheme.Modules.toUnitSection (φ ⁻¹ᵁ U) (φ.app U g) := by sorry
