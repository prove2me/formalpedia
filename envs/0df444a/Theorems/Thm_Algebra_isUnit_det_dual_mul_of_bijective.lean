-- Prove2me | Theorems.Thm_Algebra_isUnit_det_dual_mul_of_bijective
-- name    : Algebra.isUnit_det_dual_mul_of_bijective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/7280e112-d461-56a8-bd52-de710155dfca
-- title:
--   Perfect linear form gives unit Gram determinant
-- statement:
--   Let $R$ be a commutative ring, $A$ a commutative ring with an $R$-algebra structure, and let $\iota$ be a finite index type. Let $b : \iota \to A$ be a basis of $A$ as an $R$-module, and let $\tau \colon A \to R$ be an $R$-linear form. Assume that the map sending $a \in A$ to the composite of multiplication by $a$ on the left with $\tau$, that is $a \mapsto \tau(a\,\cdot\,) \in \operatorname{Hom}_R(A,R)$, is a bijection from $A$ onto the $R$-dual of $A$. The conclusion is that the determinant of the $\iota \times \iota$ matrix whose $(i,j)$ entry is $\tau(b_i b_j)$ is a unit of $R$. Note that the bijectivity hypothesis is stated for the underlying function only; $R$-linearity of $a \mapsto \tau(a\,\cdot\,)$ is automatic, so the hypothesis says exactly that $A \to \operatorname{Hom}_R(A,R)$, $a \mapsto \tau(a\,\cdot\,)$, is an isomorphism of $R$-modules.
--
--   This is the standard criterion that the Gram matrix of a perfect (trace-like) linear form on a finite free algebra has invertible determinant; the relevant case is $\tau$ a trace form, where the determinant is the discriminant. It is used in the computation relating the discriminant of a square presentation to the norm of its Jacobian determinant, via [`Algebra.associated_discr_norm_jacobianDet_of_square_presentation`](thm.html#Algebra.associated_discr_norm_jacobianDet_of_square_presentation).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_isUnit_det_dual_mul_of_bijective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.isUnit_det_dual_mul_of_bijective
    (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A) (τ : Module.Dual R A)
    (hτ : Function.Bijective (fun a : A => τ.comp (LinearMap.mulLeft R a))) :
    IsUnit (Matrix.of fun i j => τ (b i * b j)).det := by sorry
