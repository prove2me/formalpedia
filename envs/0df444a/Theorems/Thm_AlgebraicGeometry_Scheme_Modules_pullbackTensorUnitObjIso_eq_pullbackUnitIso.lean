-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackTensorUnitObjIso_eq_pullbackUnitIso
-- name    : AlgebraicGeometry.Scheme.Modules.pullbackTensorUnitObjIso_eq_pullbackUnitIso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/d8a7c40a-4129-518d-a08c-1e9446bc5023
-- title:
--   Monoidal unit comparison for f^* is the canonical one
-- statement:
--   Let $X$ and $Y$ be schemes (in a fixed universe) and let $f : X \to Y$ be a morphism of schemes. Two isomorphisms $(\,f^*\,)(\mathbf 1_{Y\text{-Mod}}) \cong \mathbf 1_{X\text{-Mod}}$ between the pullback along $f$ of the monoidal unit of the category of sheaves of modules on $Y$ and the monoidal unit on $X$ are asserted to be equal, as objects of the isomorphism type. The first, `Scheme.Modules.pullbackTensorUnitObjIso f`, is the inverse of the unit comparison isomorphism $\varepsilon$ attached to the monoidal structure on the pullback functor `Modules.pullback f`. The second, `Scheme.Modules.pullbackUnitIso f`, is the isomorphism obtained from the canonical map `SheafOfModules.pullbackObjUnitToUnit` associated with the ring-sheaf homomorphism `f.toRingCatSheafHom`, from the pullback of the unit sheaf of modules on $Y$ to the unit sheaf of modules on $X$, together with the fact that this canonical map is an isomorphism. Thus the monoidally-derived trivialisation of $f^*\mathcal O_Y$ coincides with the canonical one.
--
--   This identifies the unit constraint of the monoidal functor $f^*$ on sheaves of modules with the canonical isomorphism $f^*\mathcal O_Y \cong \mathcal O_X$, so that monoidal coherence arguments and explicit section-level computations may be used interchangeably. It is used in the development of invertible sheaves and their Čech trivialisations, for instance in the results on transition functions and on pullbacks of tensor powers, and in the rigidification data for line bundles in the relative Picard functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_pullbackTensorUnitObjIso_eq_pullbackUnitIso.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.pullbackTensorUnitObjIso_eq_pullbackUnitIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Scheme.Modules.pullbackTensorUnitObjIso f = Scheme.Modules.pullbackUnitIso f := by sorry
