-- Prove2me | Theorems.Thm_AlgHom_liftEquiv_symm_withConv_mul
-- name    : AlgHom.liftEquiv_symm_withConv_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/f10e7136-7027-509f-b25f-619adb7c44c4
-- title:
--   Base change preserves convolution of bialgebra points
-- statement:
--   Let $R$ and $S$ be commutative rings with $S$ an $R$-algebra, let $A$ be a commutative ring carrying an $R$-bialgebra structure, and let $B$ be a commutative ring which is both an $R$-algebra and an $S$-algebra, with $R \to S \to B$ a scalar tower. Mathlib's equivalence `AlgHom.liftEquiv R S A B` identifies $R$-algebra maps $A \to B$ with $S$-algebra maps $S \otimes_R A \to B$, its inverse being restriction along $a \mapsto 1 \otimes_R a$; and for a bialgebra the type of algebra maps to $B$ is given the convolution monoid structure through the type synonym `WithConv`, with `WithConv.toConv` and `WithConv.ofConv` the two transport maps. The assertion is that for all $f, g$ in `WithConv (S ⊗[R] A →ₐ[S] B)`, the restriction along $a \mapsto 1 \otimes_R a$ of the convolution product $f * g$ (computed for the base-changed bialgebra $S \otimes_R A$ over $S$) equals, as an element of the convolution monoid of $R$-algebra maps $A \to B$, the convolution product of the restrictions of $f$ and of $g$. In other words, `AlgHom.liftEquiv R S A B` is multiplicative for the convolution products on the two sides.
--
--   This is the statement that extension of scalars $R \to S$ is compatible with the group (monoid) law on the $B$-valued points of an affine scheme attached to a bialgebra, i.e. that the functor of points of $\operatorname{Spec}$ of a bialgebra commutes with base change as a monoid-valued functor. It underlies the transport of convolution-monoid structures used in the study of finite flat group schemes over $p$-adic bases, and is cited by results comparing a Hopf algebra with its base change and by the analysis of points of finite flat group schemes over discrete valuation rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgHom_liftEquiv_symm_withConv_mul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open TensorProduct in

theorem AlgHom.liftEquiv_symm_withConv_mul
    (R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
    (A : Type*) [CommRing A] [Bialgebra R A]
    (B : Type*) [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
    (f g : WithConv (S ⊗[R] A →ₐ[S] B)) :
    WithConv.toConv ((AlgHom.liftEquiv R S A B).symm (f * g).ofConv)
    = WithConv.toConv ((AlgHom.liftEquiv R S A B).symm f.ofConv)
      * WithConv.toConv ((AlgHom.liftEquiv R S A B).symm g.ofConv) := by sorry
