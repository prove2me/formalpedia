-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_exists_isClosed_mem_iff_nonempty_pullback_translation_iso
-- name    : AlgebraicGeometry.RiemannForm.exists_isClosed_mem_iff_nonempty_pullback_translation_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/1c1c70e1-8379-527b-b080-89eaf640276e
-- title:
--   Closedness of the stabiliser K(L) on an abelian scheme
-- statement:
--   Let $k$ be an algebraically closed field, let $A$ be a scheme and $f : A \to \operatorname{Spec} k$ a morphism, and let $L$ be a relative group law on $f$, that is, a functorial group structure (multiplication, unit, inverse, with associativity, unit and inverse laws, and naturality under base change along morphisms of $k$-schemes) on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of sections of $f$ over $k$-schemes $t : T \to \operatorname{Spec} k$. Assume $L$ is commutative, i.e. $L.\mathrm{mul}$ is commutative on all such section sets, and that $f$ satisfies `AbelianSchemePropertyBundle`: $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and $f$ admits a relative group law. Let $\mathcal L$ be a module on $A$ that is invertible, in the sense that every point of $A$ has an open neighbourhood $U$ with $\mathcal L|_U$ isomorphic to the unit module of $U$. The assertion is that there exists a closed subset $Z \subseteq A$ such that for every $k$-point $Q$ of $L$ (an element of the additive group of sections of $f$ over $\operatorname{Spec}$ of the identity $k \to k$) the image of the closed point of $\operatorname{Spec} k$ under the underlying continuous map of $Q$ lies in $Z$ if and only if the pullback of $\mathcal L$ along the translation endomorphism $\mathrm{translation}\ f\ L\ Q$ of $A$ — the first component of the $L$-product of the identity section with the constant section at $Q$ — is isomorphic to $\mathcal L$.
--
--   This is the statement that the stabiliser $K(\mathcal L) = \{Q \in A(k) : T_Q^*\mathcal L \cong \mathcal L\}$ of an invertible module on an abelian variety over an algebraically closed field is cut out by a Zariski-closed subset of $A$. It is used in the development of Riemann forms and polarisations, in particular in the finiteness and triviality statements [`AlgebraicGeometry.RiemannForm.finite_setOf_nonempty_pullback_translation_iso_of_finite_torsion`](thm.html#AlgebraicGeometry.RiemannForm.finite_setOf_nonempty_pullback_translation_iso_of_finite_torsion) and [`AlgebraicGeometry.RiemannForm.forall_nonempty_pullback_translation_iso_of_forall_torsion`](thm.html#AlgebraicGeometry.RiemannForm.forall_nonempty_pullback_translation_iso_of_forall_torsion).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_exists_isClosed_mem_iff_nonempty_pullback_translation_iso.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm

theorem AlgebraicGeometry.RiemannForm.exists_isClosed_mem_iff_nonempty_pullback_translation_iso
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) :
    ∃ Z : Set A, IsClosed Z ∧ ∀ Q : L.AlgPoints hc k,
      (RelativeGroupLaw.AlgPoints.toPoint Q).1.base (IsLocalRing.closedPoint k) ∈ Z ↔
        Nonempty ((Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint Q))).obj 𝓛 ≅ 𝓛) := by sorry
