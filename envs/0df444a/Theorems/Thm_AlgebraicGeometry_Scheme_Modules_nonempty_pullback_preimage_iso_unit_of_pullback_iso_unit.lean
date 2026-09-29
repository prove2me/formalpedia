-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_preimage_iso_unit_of_pullback_iso_unit
-- name    : AlgebraicGeometry.Scheme.Modules.nonempty_pullback_preimage_iso_unit_of_pullback_iso_unit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/aee85fda-4f2a-5f90-bed1-f7ab05261112
-- title:
--   Trivialisation on an open pulls back to the preimage
-- statement:
--   Let $X$ and $Y$ be schemes (in a fixed universe), let $g \colon Y \to X$ be a morphism of schemes, let $L$ be a sheaf of modules on $X$, and let $U$ be an open subscheme of $X$, with $U.\iota \colon U \to X$ the associated open immersion. Assume given an isomorphism $e$ of sheaves of modules between the pullback of $L$ along $U.\iota$ and the unit module $\mathcal{O}_U$ on $U$, that is, the sheaf of modules over the sheaf of rings of $U$ given by the structure sheaf itself. The conclusion asserts that the type of isomorphisms between the pullback along the open immersion $(g^{-1}U).\iota \colon g^{-1}U \to Y$ of the pullback of $L$ along $g$, and the unit module $\mathcal{O}_{g^{-1}U}$ on the open subscheme $g^{-1}U$ of $Y$, is nonempty. Thus the statement is the propositional assertion that $(g^{*}L)|_{g^{-1}U}$ is trivial, with no particular isomorphism recorded in the conclusion, although the proof exhibits one.
--
--   This is the transport of a trivialisation of an invertible (or arbitrary) module along an arbitrary base change: triviality of $L$ on $U$ implies triviality of $g^{*}L$ on $g^{-1}U$. In the shape `Nonempty (… ≅ …)` it matches the rigidification datum of `RigidifiedLineBundle`, whose `rigidified` field is exactly such a nonemptiness statement, and it is used in the construction of norms of invertible modules along finite morphisms ([`AlgebraicGeometry.Scheme.Modules.exists_norm_isInvertible_tensor_pullback_normModule_of_isFinite_of_isIntegrallyClosed`](thm.html#AlgebraicGeometry.Scheme.Modules.exists_norm_isInvertible_tensor_pullback_normModule_of_isFinite_of_isIntegrallyClosed)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_preimage_iso_unit_of_pullback_iso_unit.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.nonempty_pullback_preimage_iso_unit_of_pullback_iso_unit
    {X Y : Scheme.{u}} (g : Y ⟶ X) {L : X.Modules} {U : X.Opens}
    (e : (Scheme.Modules.pullback U.ι).obj L ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    Nonempty ((Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback g).obj L) ≅
      SheafOfModules.unit (g ⁻¹ᵁ U).toScheme.ringCatSheaf) := by sorry
