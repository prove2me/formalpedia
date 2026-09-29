-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_forall_nonempty_pullback_iso_of_isPullback_pi
-- name    : AlgebraicGeometry.Scheme.Modules.exists_isInvertible_forall_nonempty_pullback_iso_of_isPullback_pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/042bcbcd-45eb-5f6a-91a3-12c4d8b34873
-- title:
--   Gluing invertible modules along a finite product base
-- statement:
--   Let $k$ be a natural number and let $C_0,\dots,C_{k-1}$ be commutative rings indexed by `Fin k`. Let $X$ be a scheme with a morphism $g : X \to \operatorname{Spec}\bigl(\prod_i C_i\bigr)$, and for each $i$ let $X_i$ be a scheme with morphisms $g_i : X_i \to \operatorname{Spec} C_i$ and $v_i : X_i \to X$ such that the square with sides $v_i$, $g_i$, $g$ and the morphism $\operatorname{Spec} C_i \to \operatorname{Spec}\bigl(\prod_j C_j\bigr)$ induced by the $i$-th projection ring homomorphism is cartesian, i.e. $X_i$ is identified with the fibre product $X \times_{\operatorname{Spec}(\prod_j C_j)} \operatorname{Spec} C_i$. Suppose given, for each $i$, a sheaf of modules $M_i$ on $X_i$ that is invertible in the sense of `Scheme.Modules.IsInvertible`: every point of $X_i$ has an open neighbourhood $U$ for which the pullback of $M_i$ along the open immersion $U \to X_i$ admits an isomorphism to the unit module on $U$. The conclusion asserts the existence of a sheaf of modules $N$ on $X$ that is invertible in the same sense and such that for every $i$ the pullback $v_i^{*}N$ is isomorphic to $M_i$; the isomorphisms are asserted only to exist (as nonemptiness of the isomorphism type), with no compatibility required between different $i$, and $N$ is not claimed to be unique.
--
--   Since $\operatorname{Spec}\bigl(\prod_i C_i\bigr)$ is the disjoint union of the $\operatorname{Spec} C_i$, the morphisms $v_i$ exhibit $X$ as the disjoint union of the $X_i$, and the statement is the resulting Zariski gluing of invertible modules along a clopen decomposition, with vacuous cocycle condition. It is used when assembling polarisation data over a product base, in particular by [`AlgebraicGeometry.Polarisation.exists_faithfullyFlat_principalSqrt_of_forall_pullback_of_isPullback_pi`](thm.html#AlgebraicGeometry.Polarisation.exists_faithfullyFlat_principalSqrt_of_forall_pullback_of_isPullback_pi) and by [`CerednikDrinfeld.QM.FakeEllipticCurve.isCanonicalPolData_pi_of_forall`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.isCanonicalPolData_pi_of_forall).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_forall_nonempty_pullback_iso_of_isPullback_pi.lean

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

theorem AlgebraicGeometry.Scheme.Modules.exists_isInvertible_forall_nonempty_pullback_iso_of_isPullback_pi
    {k : ℕ} (C : Fin k → Type) [∀ i, CommRing (C i)]
    {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of (∀ i, C i)))
    {Xi : Fin k → Scheme.{0}} (gi : ∀ i, Xi i ⟶ Spec (CommRingCat.of (C i))) (v : ∀ i, Xi i ⟶ X)
    (hv : ∀ i, IsPullback (v i) (gi i) g (Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i))))
    (M : ∀ i, (Xi i).Modules) (hM : ∀ i, Scheme.Modules.IsInvertible (M i)) :
    ∃ N : X.Modules, Scheme.Modules.IsInvertible N ∧ ∀ i, Nonempty ((Scheme.Modules.pullback (v i)).obj N ≅ M i) := by sorry
