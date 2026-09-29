-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit_monoidalV2
-- name    : AlgebraicGeometry.Scheme.Modules.IsFrameOn.nonempty_pullback_iso_unit_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/2193aa7e-7969-5ad6-891c-ab1a0ae02525
-- title:
--   A frame trivialises a module on an open subscheme
-- statement:
--   Let $X$ be a scheme and $\mathcal M$ an object of `X.Modules`, i.e. a sheaf of modules over the sheaf of rings of $X$; let $U,V$ be open subsets of $X$ and $s \in \Gamma(\mathcal M, U)$ a section. Assume `IsFrameOn s V`, which says: for every open $W$ with $W \le U$ and $W \le V$, the map $\Gamma(X,W) \to \Gamma(\mathcal M,W)$ sending $g$ to $g \cdot (s|_W)$, where $s|_W$ is the image of $s$ under the restriction map of $\mathcal M$ along $W \le U$, is bijective. Then for every open $W$ of $X$ with $W \le U$ and $W \le V$ the type of isomorphisms, in the category of sheaves of modules on the open subscheme $W$, between $(\mathrm{Scheme.Modules.pullback}\ W.\iota).obj\ \mathcal M$ — the inverse image of $\mathcal M$ along the open immersion $W.\iota : W \to X$ — and `SheafOfModules.unit` of the sheaf of rings of $W$ — the structure sheaf of $W$ viewed as a module over itself, the unit of the monoidal structure — is nonempty. The assertion is thus the mere existence of such an isomorphism, with no choice of isomorphism produced.
--
--   This is the classical statement that a nowhere-vanishing section trivialises a line bundle, in the form of the local-triviality datum occurring in the project's notion of an invertible sheaf of modules on a scheme. It is used in the computation of the ideal cutting out the zero scheme of a section from a local generator, and in the construction of filtrations of pushforwards of the unit module in the study of abelian schemes with good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit_monoidalV2.lean

import Mathlib
import Definitions.Def_PresheafOfModules_InternalHom
import Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsFrameOn.nonempty_pullback_iso_unit_monoidalV2
    {X : AlgebraicGeometry.Scheme.{u}} {M : X.Modules} {U V : X.Opens} {s : Γ(M, U)}
    (h : AlgebraicGeometry.Scheme.Modules.IsFrameOn s V) (W : X.Opens) (hWU : W ≤ U) (hWV : W ≤ V) :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback W.ι).obj M ≅
      SheafOfModules.unit (W : AlgebraicGeometry.Scheme.{u}).ringCatSheaf) := by sorry
