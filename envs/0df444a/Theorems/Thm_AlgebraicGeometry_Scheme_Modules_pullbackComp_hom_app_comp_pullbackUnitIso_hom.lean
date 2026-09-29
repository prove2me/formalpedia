-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackComp_hom_app_comp_pullbackUnitIso_hom
-- name    : AlgebraicGeometry.Scheme.Modules.pullbackComp_hom_app_comp_pullbackUnitIso_hom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/87e0ad2b-0ba3-535f-b327-13afd6704711
-- title:
--   Unit trivialisations of pullbacks are compatible with composition
-- statement:
--   Let $X$, $Y$, $Z$ be schemes (in a fixed universe) and let $f\colon X\to Y$ and $g\colon Y\to Z$ be morphisms of schemes, where $f \gg g$ denotes the composite $f$ followed by $g$. For a morphism $h\colon S\to T$, `Scheme.Modules.pullbackUnitIso h` is the isomorphism $h^{*}\mathcal{O}_T \cong \mathcal{O}_S$ of sheaves of modules obtained by taking `asIso` of the canonical map `SheafOfModules.pullbackObjUnitToUnit` attached to the induced map of sheaves of rings `h.toRingCatSheafHom`, which is an isomorphism; here $\mathcal{O}_S$ means the unit object `SheafOfModules.unit S.ringCatSheaf` for the sheaf of rings of $S$. Let `Scheme.Modules.pullbackComp f g` be the comparison isomorphism of functors between $f^{*}\circ g^{*}$ and $(f\gg g)^{*}$ on sheaves of modules. The assertion is the equality of two morphisms $f^{*}g^{*}\mathcal{O}_Z \to \mathcal{O}_X$: the component of the forward direction of `pullbackComp f g` at $\mathcal{O}_Z$, followed by the forward direction of the trivialisation for $f\gg g$, coincides with the image under $f^{*}$ of the forward direction of the trivialisation for $g$, followed by the forward direction of the trivialisation for $f$.
--
--   This is a coherence statement for the inverse-image pseudofunctor on sheaves of modules over schemes: the canonical trivialisations $h^{*}\mathcal{O}\cong\mathcal{O}$ form a compatible family, so that one-step and two-step pullbacks of the structure sheaf are identified in the same way. It is used when comparing transports of rigidifications along sections, for instance in the cocycle computations for rigidified line bundles and in the Čech trivialisation machinery of the relative Picard functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_pullbackComp_hom_app_comp_pullbackUnitIso_hom.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.pullbackComp_hom_app_comp_pullbackUnitIso_hom
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Scheme.Modules.pullbackComp f g).hom.app (SheafOfModules.unit Z.ringCatSheaf) ≫
        (Scheme.Modules.pullbackUnitIso (f ≫ g)).hom =
      (Scheme.Modules.pullback f).map (Scheme.Modules.pullbackUnitIso g).hom ≫
        (Scheme.Modules.pullbackUnitIso f).hom := by sorry
