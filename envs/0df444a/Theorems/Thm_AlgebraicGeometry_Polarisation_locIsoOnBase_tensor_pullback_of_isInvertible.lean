-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_tensor_pullback_of_isInvertible
-- name    : AlgebraicGeometry.Polarisation.locIsoOnBase_tensor_pullback_of_isInvertible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/9af65271-119c-5b7c-b5aa-e11d58a36ae5
-- title:
--   Tensoring with a line bundle pulled back from the base is locally trivial
-- statement:
--   Let $B$ be a commutative ring, $P$ a scheme and $q \colon P \to \operatorname{Spec} B$ a morphism of schemes. Let $L$ be a sheaf of modules on $P$ and $N$ a sheaf of modules on $\operatorname{Spec} B$, and suppose $N$ satisfies `Scheme.Modules.IsInvertible`, i.e. every point of $\operatorname{Spec} B$ has an open neighbourhood $U$ such that the pullback of $N$ along the inclusion $U \hookrightarrow \operatorname{Spec} B$ is isomorphic to the unit module (the structure sheaf) of $U$. The conclusion is `LocIsoOnBase q (L ⊗ (Scheme.Modules.pullback q).obj N) L`: for every point $s$ of $\operatorname{Spec} B$ there exist an open $U \subseteq \operatorname{Spec} B$ with $s \in U$ and an isomorphism of sheaves of modules on the open subscheme $q^{-1}U$ between the pullback of $L \otimes q^{*}N$ along the inclusion $q^{-1}U \hookrightarrow P$ and the pullback of $L$ along that same inclusion. No hypothesis is imposed on $L$; note that the local triviality is required only over opens of the base, and the isomorphism is asserted to exist (as a `Nonempty` type) rather than produced canonically.
--
--   This records that twisting an arbitrary module by the pullback of an invertible module from an affine base is invisible Zariski-locally on the base. It is used in the construction of rigidified line bundles for the relative Picard functor and polarisation/Rosati formalism, being cited by [`AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_forall_locIsoOnBase_pullback_of_forall_away_of_locIsoOnBase`](thm.html#AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_forall_locIsoOnBase_pullback_of_forall_away_of_locIsoOnBase).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_tensor_pullback_of_isInvertible.lean

import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Polarisation

universe u

theorem AlgebraicGeometry.Polarisation.locIsoOnBase_tensor_pullback_of_isInvertible
    {B : Type u} [CommRing B] {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of B))
    (L : P.Modules) (N : (Spec (CommRingCat.of B)).Modules) (hN : Scheme.Modules.IsInvertible N) :
    LocIsoOnBase q (L ⊗ (Scheme.Modules.pullback q).obj N) L := by sorry
