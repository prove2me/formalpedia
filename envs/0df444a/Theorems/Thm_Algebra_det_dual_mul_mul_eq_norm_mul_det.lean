-- Prove2me | Theorems.Thm_Algebra_det_dual_mul_mul_eq_norm_mul_det
-- name    : Algebra.det_dual_mul_mul_eq_norm_mul_det
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/5e5f9c47-a49a-511e-a813-d54f5d65e312
-- title:
--   Twisting a trace-like form multiplies its Gram determinant by the norm
-- statement:
--   Let $R$ be a commutative ring and $A$ a commutative $R$-algebra, let $\iota$ be a finite index type, and let $b : \iota \to A$ be an $R$-basis of $A$ indexed by $\iota$. Let $\tau \colon A \to R$ be an $R$-linear form on $A$ (an element of `Module.Dual R A`) and let $c \in A$. The assertion is the equality of determinants of the two $\iota \times \iota$ matrices over $R$ with entries $\tau(c \cdot b_i \cdot b_j)$ and $\tau(b_i b_j)$ respectively: $$\det\bigl(\tau(c\, b_i b_j)\bigr)_{i,j} = \mathrm{N}_{A/R}(c) \cdot \det\bigl(\tau(b_i b_j)\bigr)_{i,j},$$ where $\mathrm{N}_{A/R}(c)$ is `Algebra.norm R c`, the determinant of the $R$-linear endomorphism $x \mapsto cx$ of $A$. No further hypotheses are imposed on $R$, $A$, $\tau$ or $c$: in particular $\tau$ is an arbitrary linear form, not assumed to be the trace form, and the bilinear forms involved need not be nondegenerate.
--
--   This is the standard behaviour of the Gram determinant of a trace-like symmetric bilinear form $(x,y) \mapsto \tau(xy)$ on a free $R$-algebra under twisting by an element $c$, the basic multiplicativity behind discriminant computations. It is used in the project to compare the discriminant of a square presentation with the norm of its Jacobian determinant, via [`Algebra.associated_discr_norm_jacobianDet_of_square_presentation`](thm.html#Algebra.associated_discr_norm_jacobianDet_of_square_presentation).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_det_dual_mul_mul_eq_norm_mul_det.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.det_dual_mul_mul_eq_norm_mul_det
    (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A) (τ : Module.Dual R A) (c : A) :
    (Matrix.of fun i j => τ (c * b i * b j)).det = Algebra.norm R c * (Matrix.of fun i j => τ (b i * b j)).det := by sorry
