-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_of_forall_locIsoOnBase_pullback_of_isPullback_pi
-- name    : AlgebraicGeometry.Polarisation.locIsoOnBase_of_forall_locIsoOnBase_pullback_of_isPullback_pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/f68f3036-ced4-55fe-a355-58c54170c33b
-- title:
--   Locality of module isomorphy over a finite product base
-- statement:
--   Let $k$ be a natural number and $C_0,\dots,C_{k-1}$ a family of commutative rings indexed by $\mathrm{Fin}\,k$, let $X$ be a scheme with a morphism $g : X \to \operatorname{Spec}\bigl(\prod_i C_i\bigr)$, and let $M, M'$ be sheaves of modules on $X$. Suppose given schemes $X_i$ with morphisms $g_i : X_i \to \operatorname{Spec} C_i$ and $v_i : X_i \to X$ such that for each $i$ the square formed by $v_i$, $g_i$, $g$ and $\operatorname{Spec}$ of the $i$-th evaluation homomorphism $\prod_j C_j \to C_i$ is cartesian, and suppose that for each $i$ the predicate `LocIsoOnBase` holds for $g_i$ and the pullbacks $v_i^*M$, $v_i^*M'$, that is: every point $y$ of $\operatorname{Spec} C_i$ has an open neighbourhood $U_i$ such that the restrictions of $v_i^*M$ and $v_i^*M'$ along the inclusion of the open subscheme $g_i^{-1}U_i$ into $X_i$ are isomorphic as modules. The conclusion is `LocIsoOnBase` for $g$, $M$, $M'$: every point $s$ of $\operatorname{Spec}\bigl(\prod_i C_i\bigr)$ has an open neighbourhood $U$ such that the pullbacks of $M$ and of $M'$ along the inclusion of $g^{-1}U$ into $X$ are isomorphic.
--
--   This is the statement that the local-isomorphy clause occurring in the notion of a polarised abelian scheme descends from the factors of a finite product of base rings to the product itself, the $X_i$ being the clopen pieces of $X$ cut out by the idempotents of $\prod_i C_i$. It is used in the assembly of polarisation data over a product base, being cited by the corresponding statements for the existence of a faithfully flat principal square root and for Rosati compatibility, and by the construction of canonical polarisation data for fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_of_forall_locIsoOnBase_pullback_of_isPullback_pi.lean

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

theorem AlgebraicGeometry.Polarisation.locIsoOnBase_of_forall_locIsoOnBase_pullback_of_isPullback_pi
    {k : ℕ} (C : Fin k → Type) [∀ i, CommRing (C i)]
    {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of (∀ i, C i))) (M M' : X.Modules)
    {Xi : Fin k → Scheme.{0}} (gi : ∀ i, Xi i ⟶ Spec (CommRingCat.of (C i))) (v : ∀ i, Xi i ⟶ X)
    (hv : ∀ i, IsPullback (v i) (gi i) g (Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i))))
    (h : ∀ i, LocIsoOnBase (gi i) ((Scheme.Modules.pullback (v i)).obj M) ((Scheme.Modules.pullback (v i)).obj M')) :
    LocIsoOnBase g M M' := by sorry
