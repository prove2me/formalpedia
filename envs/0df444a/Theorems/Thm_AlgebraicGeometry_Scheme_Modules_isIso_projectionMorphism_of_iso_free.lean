-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_projectionMorphism_of_iso_free
-- name    : AlgebraicGeometry.Scheme.Modules.isIso_projectionMorphism_of_iso_free
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/d44e9d2b-1894-520c-8ae6-14e83134a0b1
-- title:
--   Projection formula for free modules of finite rank
-- statement:
--   Let $Z$ and $X$ be schemes (in a fixed universe), let $i\colon Z\to X$ be a morphism of schemes, let $n$ be a natural number, and let $F$ be an object of `X.Modules`, the category of sheaves of modules over the structure sheaf of $X$. Assume given an isomorphism $e$ from $F$ to `SheafOfModules.free (ULift (Fin n))`, the free sheaf of modules on an index type with $n$ elements, so that $F$ is free of rank $n$. The conclusion is that the projection morphism `Scheme.Modules.projectionMorphism i F` is an isomorphism. Here that morphism is the map $$i_*(\mathbf 1_{Z}) \otimes F \longrightarrow i_*\bigl(i^*F\bigr)$$ obtained by transposing, along the adjunction between $i^*$ and $i_*$ on modules, the morphism $i^*\bigl(i_*(\mathbf 1_Z)\otimes F\bigr)\to i^*F$ given by the inverse of the monoidal comparison isomorphism for $i^*$ at the pair $(i_*(\mathbf 1_Z), F)$, followed by whiskering the counit of the adjunction at the unit object on the left of $i^*F$, followed by the left unitor. No hypothesis beyond the existence of the isomorphism $e$ is imposed on $i$.
--
--   This is the free case of the projection formula: for $F\cong\mathcal O_X^{\oplus n}$ the natural map $i_*\mathcal O_Z\otimes F\to i_*i^*F$ is invertible, for an arbitrary morphism $i$. It is used, via the naturality of the projection morphism in $F$, to obtain the projection formula for closed immersions and thence the short exact sequences attached to invertible ideal sheaves and their thickenings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_isIso_projectionMorphism_of_iso_free.lean

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_ModulesProjectionMorphism

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.isIso_projectionMorphism_of_iso_free
    {Z X : Scheme.{u}} (i : Z ⟶ X) {n : ℕ} (F : X.Modules)
    (e : F ≅ SheafOfModules.free.{u} (ULift.{u} (Fin n))) :
    IsIso (Scheme.Modules.projectionMorphism i F) := by sorry
