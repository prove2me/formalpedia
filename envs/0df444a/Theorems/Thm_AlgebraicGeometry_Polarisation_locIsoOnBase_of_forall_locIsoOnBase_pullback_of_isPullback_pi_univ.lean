-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_of_forall_locIsoOnBase_pullback_of_isPullback_pi_univ
-- name    : AlgebraicGeometry.Polarisation.locIsoOnBase_of_forall_locIsoOnBase_pullback_of_isPullback_pi_univ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/09f93bd4-7948-52d4-a5df-13f3b07049db
-- title:
--   LocIsoOnBase descends from the clopen pieces of a product base
-- statement:
--   Let $k$ be a natural number and $C_0,\dots,C_{k-1}$ a family of commutative rings indexed by `Fin k`. Let $X$ be a scheme with a morphism $g : X \to \operatorname{Spec}\bigl(\prod_i C_i\bigr)$, and let $M, M'$ be sheaves of modules on $X$ (objects of `X.Modules`). Suppose given, for each $i$, a scheme $X_i$ with morphisms $g_i : X_i \to \operatorname{Spec} C_i$ and $v_i : X_i \to X$ such that the square formed by $v_i$, $g_i$, $g$ and $\operatorname{Spec}$ of the $i$-th projection $\prod_j C_j \to C_i$ is cartesian. Assume that for each $i$ the pullbacks $v_i^{*}M$ and $v_i^{*}M'$ satisfy `LocIsoOnBase` over $g_i$, that is: every point $t$ of $\operatorname{Spec} C_i$ has an open neighbourhood $U_i$ such that the restrictions of $v_i^{*}M$ and $v_i^{*}M'$ to the open subscheme $g_i^{-1}U_i$ of $X_i$, pulled back along its inclusion, are isomorphic. The conclusion is that $M$ and $M'$ satisfy `LocIsoOnBase` over $g$: every point $s$ of $\operatorname{Spec}\bigl(\prod_i C_i\bigr)$ has an open neighbourhood $U$ with the pullbacks of $M$ and $M'$ along the inclusion of $g^{-1}U$ into $X$ isomorphic.
--
--   The property `LocIsoOnBase` is the clause, occurring in the treatment of polarisations, that two sheaves of modules on $X$ become isomorphic after restriction over a suitable open neighbourhood of each point of the base. The statement says that this property may be checked on the clopen pieces $\operatorname{Spec} C_i$ of a base which is the spectrum of a finite product of rings; it is used in [`GoodReductionJacobian.RelativeGroupLaw.principalSqrt_pi_of_forall`](thm.html#GoodReductionJacobian.RelativeGroupLaw.principalSqrt_pi_of_forall).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_of_forall_locIsoOnBase_pullback_of_isPullback_pi_univ.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation

universe u

theorem AlgebraicGeometry.Polarisation.locIsoOnBase_of_forall_locIsoOnBase_pullback_of_isPullback_pi_univ
    {k : ℕ} (C : Fin k → Type u) [∀ i, CommRing (C i)]
    {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of (∀ i, C i))) (M M' : X.Modules)
    {Xi : Fin k → Scheme.{u}} (gi : ∀ i, Xi i ⟶ Spec (CommRingCat.of (C i))) (v : ∀ i, Xi i ⟶ X)
    (hv : ∀ i, IsPullback (v i) (gi i) g (Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i))))
    (h : ∀ i, LocIsoOnBase (gi i) ((Scheme.Modules.pullback (v i)).obj M) ((Scheme.Modules.pullback (v i)).obj M')) :
    LocIsoOnBase g M M' := by sorry
