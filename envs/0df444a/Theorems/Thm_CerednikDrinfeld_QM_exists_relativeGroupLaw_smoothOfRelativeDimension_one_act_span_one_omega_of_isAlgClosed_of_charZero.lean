-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_exists_relativeGroupLaw_smoothOfRelativeDimension_one_act_span_one_omega_of_isAlgClosed_of_charZero
-- name    : CerednikDrinfeld.QM.exists_relativeGroupLaw_smoothOfRelativeDimension_one_act_span_one_omega_of_isAlgClosed_of_charZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/520bb7d0-90be-503e-9dcb-d00048853d57
-- title:
--   Elliptic curve over k with an action of ℤ[ω]
-- statement:
--   Let $k$ be an algebraically closed field of characteristic zero and let $\omega \in k$ satisfy $\omega^2 + \omega + 1 = 0$; write $O := \operatorname{span}_{\mathbb Z}\{1,\omega\} \subseteq k$. The assertion is that there exist a scheme $A$, a morphism $f : A \to \operatorname{Spec} k$ and a relative group law $L$ for $f$ — that is, an operation on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of sections over each $t : T \to \operatorname{Spec} k$, with unit, inverse, associativity, unit and inverse laws, compatible with precomposition in $T$ — such that $L$ is commutative, $f$ is smooth and proper with connected fibres and admits a relative group law, $f$ is smooth of relative dimension $1$, and moreover there is a family $\varepsilon : O \to \operatorname{Hom}(A,A)$ with $\varepsilon(x)$ followed by $f$ equal to $f$ for all $x$, satisfying: postcomposition with $\varepsilon(x)$ is an endomorphism of $L$ on sections over every base $t : T \to \operatorname{Spec} k$; $\varepsilon(1) = \mathrm{id}_A$; $\varepsilon(xy)$ equals $\varepsilon(y)$ followed by $\varepsilon(x)$ whenever $xy \in O$; and on sections $\varepsilon(x+y)(P) = L(\varepsilon(x)(P), \varepsilon(y)(P))$.
--
--   This supplies an elliptic curve over an algebraically closed field of characteristic zero with complex multiplication by $\mathbb Z[\omega]$, packaged as a commutative abelian scheme of relative dimension one over $\operatorname{Spec} k$ together with a unital ring action of the order $\operatorname{span}_{\mathbb Z}\{1,\omega\}$ by endomorphisms over the base. It is used in the construction of a fake elliptic curve for the indefinite quaternion algebra ramified exactly at $2$ and $3$ over the algebraic closure of $\mathbb Q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_exists_relativeGroupLaw_smoothOfRelativeDimension_one_act_span_one_omega_of_isAlgClosed_of_charZero.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_QuaternionAlgebra_Order

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.exists_relativeGroupLaw_smoothOfRelativeDimension_one_act_span_one_omega_of_isAlgClosed_of_charZero
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (ω : k) (hω : ω ^ 2 + ω + 1 = 0) :
    ∃ (A : Scheme.{0}) (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f),
      L.IsCommutative ∧ AbelianSchemePropertyBundle k f ∧ SmoothOfRelativeDimension 1 f ∧
      ∃ (ε : ↥(Submodule.span ℤ ({1, ω} : Set k)) → (A ⟶ A)) (hε : ∀ x, ε x ≫ f = f),
        (∀ (x : ↥(Submodule.span ℤ ({1, ω} : Set k))) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k))
            (P Q : SchemeHomOver t f),
          pushPt (ε x) (hε x) (L.mul t P Q) = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε x) (hε x) Q)) ∧
        (∀ h : (1 : k) ∈ Submodule.span ℤ ({1, ω} : Set k), ε ⟨1, h⟩ = 𝟙 A) ∧
        (∀ (x y : ↥(Submodule.span ℤ ({1, ω} : Set k))) (h : (x : k) * (y : k) ∈ Submodule.span ℤ ({1, ω} : Set k)),
          ε ⟨(x : k) * (y : k), h⟩ = ε y ≫ ε x) ∧
        (∀ (x y : ↥(Submodule.span ℤ ({1, ω} : Set k))) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k))
            (P : SchemeHomOver t f),
          pushPt (ε (x + y)) (hε (x + y)) P = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε y) (hε y) P)) := by sorry
