-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_translation_tensor_dual_iso_of_mumfordBundle_iso_of_isAlgClosed
-- name    : AlgebraicGeometry.Polarisation.nonempty_pullback_translation_tensor_dual_iso_of_mumfordBundle_iso_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/2b328252-23fd-53ea-b780-3a13bc914c5c
-- title:
--   Isomorphic Mumford bundles give translation-invariant difference bundle
-- statement:
--   Let $k$ be an algebraically closed field, let $A$ be a scheme with a morphism $f : A \to \operatorname{Spec} k$, and let $L$ be a relative group law on $f$ over $k$: a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over $\operatorname{Spec} k$, natural in $T$. Let $hc$ assert that $L$ is commutative (this hypothesis enters only through the type of $Q$ below). Let $\mathcal L, \mathcal L'$ be modules on $A$, each invertible in the sense that every point has an open neighbourhood $U$ over which the restriction is isomorphic to the unit module on $U$. Write $\Lambda(\mathcal M) = m^*\mathcal M \otimes (p_1^*\mathcal M^\vee \otimes p_2^*\mathcal M^\vee)$ for the Mumford bundle on $A \times_{\operatorname{Spec} k} A$, where $m$ is the morphism given by multiplying the two projections under $L$, and $\mathcal M^\vee$ is the internal hom from $\mathcal M$ into the unit. Assume an isomorphism $\Lambda(\mathcal L) \cong \Lambda(\mathcal L')$ exists, and let $Q$ be an element of the additive group of $k$-points of $f$, with associated point $Q^{\mathrm{pt}}$. Then there exists an isomorphism $T_Q^*(\mathcal L \otimes \mathcal L'^\vee) \cong \mathcal L \otimes \mathcal L'^\vee$, where $T_Q$ is the translation morphism $A \to A$ obtained by multiplying the identity point of $A$ by the constant point $Q^{\mathrm{pt}}$ under $L$.
--
--   This is the standard step in the theory of abelian varieties showing that two invertible sheaves with isomorphic Mumford bundles differ by an element of $\operatorname{Pic}^0$, i.e. by a translation-invariant line bundle. It is used in the construction of Riemann forms, in [`AlgebraicGeometry.RiemannForm.exists_iso_tensorPow_tensor_of_forall_dvd_of_two_ne_zero`](thm.html#AlgebraicGeometry.RiemannForm.exists_iso_tensorPow_tensor_of_forall_dvd_of_two_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_translation_tensor_dual_iso_of_mumfordBundle_iso_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.nonempty_pullback_translation_tensor_dual_iso_of_mumfordBundle_iso_of_isAlgClosed
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative)
    (𝓛 𝓛' : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (h𝓛' : Scheme.Modules.IsInvertible 𝓛')
    (h : Nonempty (mumfordBundle f L 𝓛 ≅ mumfordBundle f L 𝓛')) (Q : L.AlgPoints hc k) :
    Nonempty ((Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint Q))).obj (𝓛 ⊗ Scheme.Modules.dual 𝓛') ≅
      𝓛 ⊗ Scheme.Modules.dual 𝓛') := by sorry
