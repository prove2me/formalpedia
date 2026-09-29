-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_eq_zero_of_comp_translation_eq_of_nonempty
-- name    : AlgebraicGeometry.RiemannForm.eq_zero_of_comp_translation_eq_of_nonempty
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/625ad20b-5e10-5fea-b72b-f57123e5b788
-- title:
--   Translation fixing a morphism from a non-empty scheme is trivial
-- statement:
--   Let $k$ be a field, let $A$ be a scheme and let $f : A \to \operatorname{Spec} k$ be a morphism, and let $L$ be a `RelativeGroupLaw` for $f$: for every scheme $T$ and every $t : T \to \operatorname{Spec} k$ a multiplication, unit and inverse on the set $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points of $A$ over $t$, satisfying associativity, the unit laws and left inversion, with multiplication compatible with precomposition in $T$. Let $hc$ witness that $L$ is commutative, let $Z$ be a scheme whose underlying topological space is non-empty, let $v : Z \to A$ be a morphism, and let $P$ be an element of `L.AlgPoints hc k`, that is, an element of the additive group attached to the group of points of $A$ over $\operatorname{Spec}$ of the identity map $k \to k$. Write $x$ for the point `RelativeGroupLaw.AlgPoints.toPoint P` underlying $P$, and let $\mathrm{translation}\ f\ L\ x : A \to A$ be the first component of the $L$-product of the identity point of $A$ over $f$ with the constant point $f$ followed by $x$. If $v$ followed by this translation equals $v$, then $P = 0$. The commutativity hypothesis serves only to form the type `L.AlgPoints hc k`; the argument uses the group axioms and the naturality of $L$ alone.
--
--   This is the rigidity statement that translation by a non-zero point of a relative group law acts without fixed points, in the form needed for morphisms out of a non-empty base: the only algebraic point whose translation fixes a given morphism $v$ is the zero point. It is used in the construction of descent data for torsion pullbacks of translations in the Riemann-form package.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_eq_zero_of_comp_translation_eq_of_nonempty.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm

theorem AlgebraicGeometry.RiemannForm.eq_zero_of_comp_translation_eq_of_nonempty
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative)
    {Z : Scheme.{0}} (hZ : Nonempty ↥Z) (v : Z ⟶ A) (P : L.AlgPoints hc k)
    (h : v ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint P) = v) :
    P = 0 := by sorry
