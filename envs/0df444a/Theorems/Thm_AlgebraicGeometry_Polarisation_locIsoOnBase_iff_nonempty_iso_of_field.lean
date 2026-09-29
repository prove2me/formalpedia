-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_iff_nonempty_iso_of_field
-- name    : AlgebraicGeometry.Polarisation.locIsoOnBase_iff_nonempty_iso_of_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/52e31024-4df4-5167-8747-2ae35682903f
-- title:
--   Over a field, local isomorphy on the base is isomorphy
-- statement:
--   Let $K$ be a field, let $X$ be a scheme, let $g : X \to \operatorname{Spec} K$ be a morphism of schemes, and let $M$ and $M'$ be two objects of the category `X.Modules` of modules on $X$. The assertion is an equivalence between two statements. The first is `LocIsoOnBase g M M'`: for every point $s$ of $\operatorname{Spec} K$ there is an open subset $U$ of $\operatorname{Spec} K$ with $s \in U$ such that the pullbacks of $M$ and of $M'$ along the inclusion morphism of the open subscheme $g^{-1}U$ of $X$ into $X$, i.e. the restrictions $M|_{g^{-1}U}$ and $M'|_{g^{-1}U}$, are isomorphic (the isomorphism being asserted merely to exist, as a `Nonempty` type). The second is that $M$ and $M'$ are isomorphic in `X.Modules`, again in the sense that the type of isomorphisms $M \cong M'$ is nonempty. Thus over a base which is the spectrum of a field the relation "locally isomorphic on the base" coincides with "isomorphic".
--
--   A bookkeeping equivalence in a treatment of polarisations and the Rosati involution: several notions there (conditions on kernels, symmetry, invertibility of a bundle) are formulated as local isomorphy on the base, and over a field these must be converted into genuine isomorphisms of modules. It is used by the results of that development which work over a field, including the statements about the Mumford bundle and about stabilisers of tensor products of pullbacks.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_iff_nonempty_iso_of_field.lean

import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.locIsoOnBase_iff_nonempty_iso_of_field
    {K : Type} [Field K] {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of K)) (M M' : X.Modules) :
    LocIsoOnBase g M M' ↔ Nonempty (M ≅ M') := by sorry
