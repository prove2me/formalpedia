-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection
-- name    : AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/39981599-2a1f-5851-b13a-3a1fc7c0f3f2
-- title:
--   Trivialisation of φ^*mathcal O_Y on pulled-back functions
-- statement:
--   Let $\varphi : X \to Y$ be a morphism of schemes, let $U$ be an open subset of $Y$ and let $g \in \Gamma(Y, U)$ be a section of the structure sheaf of $Y$ over $U$. Write $g$ also for the corresponding section over $U$ of the unit object of the monoidal category $Y.\mathrm{Modules}$ of sheaves of modules on $Y$, that is, `toUnitSection U g`, which is $g$ itself. Applying the component at $U$ of the unit of the pullback–pushforward adjunction `Modules.pullbackPushforwardAdjunction φ` yields the section `pullbackLocalSection φ` of $(\mathrm{Modules.pullback}\ \varphi).\mathrm{obj}$ of the unit module, over the preimage $\varphi^{-1}U$. The assertion is that evaluating at $\varphi^{-1}U$ the component of the canonical isomorphism `Scheme.Modules.pullbackUnitIso φ`, from $\varphi^*$ of the unit module on $Y$ to the unit module on $X$ (the inverse of an isomorphism coming from `SheafOfModules.pullbackObjUnitToUnit` applied to the induced map of sheaves of rings), sends this section to $\varphi^\sharp(g) =$ `φ.app U g`, regarded as a section of the unit module over $\varphi^{-1}U$.
--
--   This pins down the canonical trivialisation $\varphi^*\mathcal O_Y \cong \mathcal O_X$ by its effect on pulled-back functions, thereby excluding twisted trivialisations. It is used in the treatment of rigidified line bundles and the relative Picard functor, for instance in the computations with invertible modules on schemes obtained by gluing lines and in the projective presentations of polarised abelian schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection
    {X Y : Scheme.{u}} (φ : X ⟶ Y) (U : Y.Opens) (g : Γ(Y, U)) :
    (Scheme.Modules.pullbackUnitIso φ).hom.app (φ ⁻¹ᵁ U)
        (Scheme.Modules.pullbackLocalSection φ (Scheme.Modules.toUnitSection U g)) =
      Scheme.Modules.toUnitSection (φ ⁻¹ᵁ U) (φ.app U g) := by sorry
