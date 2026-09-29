-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_unit_of_isOpenImmersion_of_uniqueFactorizationMonoid
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_unit_of_isOpenImmersion_of_uniqueFactorizationMonoid
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/3cb81559-7914-5781-a127-d629d0d49b73
-- title:
--   Line bundles on open subschemes of Spec of a UFD are trivial
-- statement:
--   Let $B$ be a commutative ring which is a domain with unique factorisation, let $Y$ be a scheme, and let $g\colon Y\to\operatorname{Spec} B$ be a morphism which is an open immersion. Let $L$ be an object of $Y.\mathrm{Modules}$, the category of sheaves of modules over the sheaf of rings of $Y$, and suppose $L$ satisfies `Scheme.Modules.IsInvertible`: for every point $x$ of $Y$ there is an open subset $U$ of $Y$ with $x\in U$ such that the pullback of $L$ along the inclusion $U.\iota\colon U\to Y$ is isomorphic, as a sheaf of modules on $U$, to the unit object `SheafOfModules.unit` of the ring sheaf of $U$ (that is, $L$ admits a local frame near every point). The conclusion asserts that the type of isomorphisms $L\cong$ `SheafOfModules.unit Y.ringCatSheaf` in $Y.\mathrm{Modules}$ is nonempty: $L$ is globally isomorphic to the structure sheaf of $Y$ viewed as a module over itself. The statement is the existence of such an isomorphism, with no isomorphism chosen or constructed as data.
--
--   This is the vanishing of the Picard group of any open subscheme of the spectrum of a unique factorisation domain, in the form 'every locally free rank one module sheaf is trivial'. It feeds the local version [`AlgebraicGeometry.Scheme.Modules.exists_mem_nonempty_pullback_inf_iso_unit_of_uniqueFactorizationMonoid_stalk`](thm.html#AlgebraicGeometry.Scheme.Modules.exists_mem_nonempty_pullback_inf_iso_unit_of_uniqueFactorizationMonoid_stalk), used in the treatment of relative Picard functors and rigidified line bundles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_unit_of_isOpenImmersion_of_uniqueFactorizationMonoid.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_unit_of_isOpenImmersion_of_uniqueFactorizationMonoid
    {B : Type u} [CommRing B] [IsDomain B] [UniqueFactorizationMonoid B]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of B)) [IsOpenImmersion g]
    {L : Y.Modules} (hL : Scheme.Modules.IsInvertible L) :
    Nonempty (L ≅ SheafOfModules.unit Y.ringCatSheaf) := by sorry
