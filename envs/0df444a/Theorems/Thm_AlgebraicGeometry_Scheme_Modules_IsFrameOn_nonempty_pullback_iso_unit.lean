-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit
-- name    : AlgebraicGeometry.Scheme.Modules.IsFrameOn.nonempty_pullback_iso_unit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/1df3fb7e-a9f9-550a-8588-33cf2221b201
-- title:
--   A frame trivialises a module on an open subset
-- statement:
--   Let $X$ be a scheme and $M$ a sheaf of modules over the sheaf of rings of $X$, let $U,V\subseteq X$ be open and let $s\in\Gamma(M,U)$. Assume `IsFrameOn s V`, that is: for every open $W$ with $W\le U$ and $W\le V$ the map $\Gamma(X,W)\to\Gamma(M,W)$, $g\mapsto g\cdot(s|_W)$, given by scalar multiplication by the restriction of $s$ along $W\le U$, is bijective. Then for every open $W\le U$ with $W\le V$ the type of isomorphisms, in the category of sheaves of modules on the open subscheme $W$, between the pullback of $M$ along the open immersion $W.\iota \colon W\to X$ and the unit object `SheafOfModules.unit` of the sheaf of rings of $W$ is nonempty. So the assertion is the existence of an isomorphism $M|_W\cong \mathcal O_W$ of $\mathcal O_W$-modules, with no particular isomorphism produced as data.
--
--   This is the classical statement that a section which generates freely on an open set trivialises the module there, in the form of the local-triviality datum used in the project's notion of an invertible sheaf of modules. It is used, for instance, to produce local trivialisations from frames on finitely many affine opens, and in the constructions surrounding projective space and the relative Picard functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit.lean

import Mathlib
import Definitions.Def_PresheafOfModules_InternalHom
import Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsFrameOn.nonempty_pullback_iso_unit
    {X : AlgebraicGeometry.Scheme.{u}} {M : X.Modules} {U V : X.Opens} {s : Γ(M, U)}
    (h : AlgebraicGeometry.Scheme.Modules.IsFrameOn s V) (W : X.Opens) (hWU : W ≤ U) (hWV : W ≤ V) :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback W.ι).obj M ≅
      SheafOfModules.unit (W : AlgebraicGeometry.Scheme.{u}).ringCatSheaf) := by sorry
