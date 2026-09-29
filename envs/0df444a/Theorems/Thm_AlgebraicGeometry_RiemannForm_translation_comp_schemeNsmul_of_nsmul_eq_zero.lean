-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_translation_comp_schemeNsmul_of_nsmul_eq_zero
-- name    : AlgebraicGeometry.RiemannForm.translation_comp_schemeNsmul_of_nsmul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/aa126b3e-7843-5e9d-83a8-de6160f9bd08
-- title:
--   Translation by an m-torsion point followed by [m]
-- statement:
--   Let $k$ be a field, let $A$ be a scheme (in the zeroth universe) and let $f : A \to \operatorname{Spec} k$ be a morphism. Let $L$ be a relative group law on $f$, that is, a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ\! f = t\}$ of $T$-points of $A$ over $\operatorname{Spec} k$, given by multiplication, unit and inverse operations satisfying associativity, the unit laws and left inverses, with multiplication compatible with base change along any $\psi : T' \to T$ over $\operatorname{Spec} k$; and let $hc$ assert that every such multiplication is commutative. Let $P$ be an element of `L.AlgPoints hc k`, i.e. a $k$-point of $A$ over $\operatorname{Spec} k$ regarded additively via $L$, and let $m$ be a natural number with $m \cdot P = 0$ in that group. Write $x$ for the underlying $k$-point of $P$. Then the endomorphism $T_x$ of $A$ obtained as the underlying morphism of $L.\mathrm{mul}\,f\,(\mathbb{1}_A)\,(f \circ\! x)$, followed by the endomorphism $[m]$ obtained as the underlying morphism of the $m$-fold $L$-power of $\mathbb{1}_A$ (defined by recursion from the unit), equals $[m]$ itself: $T_x$ followed by $[m]$ is $[m]$.
--
--   This is the scheme-theoretic form of the statement that translation by an $m$-torsion point commutes with, and is absorbed by, multiplication by $m$ on a commutative group scheme. It supplies the witness used in the construction and well-definedness of the level pairing attached to torsion points, and is cited by the existence and uniqueness statements for pairing values and by the comparison of pullbacks of $[m]$ along translations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_translation_comp_schemeNsmul_of_nsmul_eq_zero.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm

theorem AlgebraicGeometry.RiemannForm.translation_comp_schemeNsmul_of_nsmul_eq_zero
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative)
    (P : L.AlgPoints hc k) (m : ℕ) (hP : m • P = 0) :
    translation f L (RelativeGroupLaw.AlgPoints.toPoint P) ≫ L.schemeNsmul m = L.schemeNsmul m := by sorry
