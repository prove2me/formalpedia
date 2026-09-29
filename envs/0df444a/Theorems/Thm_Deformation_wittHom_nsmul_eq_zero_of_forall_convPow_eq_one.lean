-- Prove2me | Theorems.Thm_Deformation_wittHom_nsmul_eq_zero_of_forall_convPow_eq_one
-- name    : Deformation.wittHom_nsmul_eq_zero_of_forall_convPow_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/a759971e-0ab3-57cc-a76b-c76485fd1175
-- title:
--   Truncated Witt homomorphisms killed by the exponent
-- statement:
--   Let $R$ be a commutative ring, let $p$ be a prime (as a `Fact`), let $n$ be a natural number, and let $A$ be a commutative ring carrying an $R$-bialgebra structure. Let $m$ be a natural number, and assume the hypothesis `hA`: for every type $T$ in the same universe as $A$, equipped with a commutative ring structure and an $R$-algebra structure, every element $f$ of `WithConv (A →ₐ[R] T)`, i.e. every $R$-algebra homomorphism $A \to T$ regarded as a point of the convolution monoid, satisfies $f^m = 1$. Let $x$ be an element of [`Deformation.wittHom R p n A`](def/Dieudonne_WittVectorHom.html#L246), the additive subgroup of $\mathrm{TruncatedWittVector}\ p\ n\ A$ consisting of those truncated Witt vectors $y$ for which the functorial map induced by the comultiplication $A \to A \otimes_R A$ satisfies $W(\Delta)(y) = W(\iota_1)(y) + W(\iota_2)(y)$, where $\iota_1, \iota_2$ are the two inclusions of $A$ into $A \otimes_R A$. Then $m \cdot x = 0$ in that subgroup.
--
--   In the Dieudonné-theoretic reading, elements of [`Deformation.wittHom R p n A`](def/Dieudonne_WittVectorHom.html#L246) are the homomorphisms from $\operatorname{Spec} A$ to the additive group of Witt vectors of length $n$, and the statement says that this group of homomorphisms is killed by any exponent $m$ of the point functor of $\operatorname{Spec} A$; for a finite commutative group scheme this gives that its Dieudonné module is killed by the exponent, hence by the order, of the group scheme. It feeds the counting of primitives modulo Verschiebung used in the finite flat local theory.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_wittHom_nsmul_eq_zero_of_forall_convPow_eq_one.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem Deformation.wittHom_nsmul_eq_zero_of_forall_convPow_eq_one
    {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] {n : ℕ}
    {A : Type v} [CommRing A] [Bialgebra R A] (m : ℕ)
    (hA : ∀ (T : Type v) [CommRing T] [Algebra R T] (f : WithConv (A →ₐ[R] T)), f ^ m = 1)
    (x : Deformation.wittHom R p n A) : m • x = 0 := by sorry
