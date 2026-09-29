-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_translation_eq_translate_toUnitPt_and_translate_eq_translation_ofUnitPt
-- name    : AlgebraicGeometry.RiemannForm.translation_eq_translate_toUnitPt_and_translate_eq_translation_ofUnitPt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/f2d4199c-bf1d-5b74-a4a7-b43e06e8a4ce
-- title:
--   Translation by a point: two spellings agree
-- statement:
--   Let $k$ be a field, let $A$ be a scheme and let $f : A \to \operatorname{Spec} k$ be a morphism, equipped with a relative group law $L$ on $f$ in the sense of `RelativeGroupLaw`: functorial multiplication, unit and inverse operations on the sets $\{\varphi : T \to A \mid \varphi \text{ followed by } f = t\}$ of $T$-points over each $t : T \to \operatorname{Spec} k$, satisfying associativity, the two unit laws, left inversion, and compatibility with base change along morphisms $\psi : T' \to T$ over $\operatorname{Spec} k$. Two sets of $k$-points of $A$ are in play: `Pt f`, the morphisms $x : \operatorname{Spec} k \to A$ with $x$ followed by $f$ equal to $\operatorname{Spec}$ of the identity map $k \to k$, and the morphisms $y$ with $y$ followed by $f$ equal to the identity of $\operatorname{Spec} k$; the maps `toUnitPt` and `ofUnitPt` pass between them, keeping the underlying morphism and adjusting only the compatibility datum. The assertion is the conjunction of two identities of endomorphisms of $A$: for every $x$ in `Pt f`, the Riemann-form translation $\mathrm{translation}\ f\ L\ x$, namely the underlying morphism of $L.\mathrm{mul}\ f$ applied to the identity point and to $f$ followed by $x$, equals $L.\mathrm{translate}$ of `toUnitPt f x`; and for every $y$ over the identity, $L.\mathrm{translate}\ y$ equals $\mathrm{translation}\ f\ L$ of `ofUnitPt f y`.
--
--   This is the classical translation endomorphism $T_x$ of an abelian variety (or of a scheme with a relative group law), recorded in the two typings of a $k$-point that occur in the development. It serves as a bridge so that results proved about `RiemannForm.translation` can be invoked where translations are written via `RelativeGroupLaw.translate`, and is used in the treatment of polarisations, Riemann forms and Euler characteristics, and in the Čerednik–Drinfeld fake elliptic curve material.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_translation_eq_translate_toUnitPt_and_translate_eq_translation_ofUnitPt.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm

theorem AlgebraicGeometry.RiemannForm.translation_eq_translate_toUnitPt_and_translate_eq_translation_ofUnitPt
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f) :
    (∀ x : Pt f, translation f L x = L.translate (toUnitPt f x)) ∧
    (∀ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f, L.translate y = translation f L (ofUnitPt f y)) := by sorry
