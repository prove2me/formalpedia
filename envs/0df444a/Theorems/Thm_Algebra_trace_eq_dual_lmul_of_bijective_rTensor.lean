-- Prove2me | Theorems.Thm_Algebra_trace_eq_dual_lmul_of_bijective_rTensor
-- name    : Algebra.trace_eq_dual_lmul_of_bijective_rTensor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/96d0bd9a-6ad7-5b11-b102-f318f862f81c
-- title:
--   Trace formula via a balanced Casimir element
-- statement:
--   Let $R$ be a commutative ring and $A$ a commutative $R$-algebra which is finite and free as an $R$-module. Let $\tau \colon A \to R$ be an $R$-linear form and let $\Delta \in A \otimes_R A$ satisfy the balancing condition $(s \otimes 1)\,\Delta = (1 \otimes s)\,\Delta$ for every $s \in A$, the product being taken in the $R$-algebra $A \otimes_R A$. Write $\theta(\varphi)$ for the element of $A$ obtained from $\varphi \in \operatorname{Hom}_R(A,R)$ by applying $\varphi$ to the left tensor factor of $\Delta$ and identifying $R \otimes_R A$ with $A$. Assume that $\theta \colon \operatorname{Hom}_R(A,R) \to A$ is bijective and that $\theta(\tau) = 1$. Then for every $x \in A$ the $R$-linear trace of multiplication by $x$ on $A$ is given by $\operatorname{Tr}_{A/R}(x) = \tau\bigl(\mu(\Delta)\, x\bigr)$, where $\mu \colon A \otimes_R A \to A$ is the multiplication map.
--
--   This is the Scheja–Storch trace formula for a Frobenius-algebra structure on $A$: the trace form is the linear form $\tau$ twisted by the image $\mu(\Delta)$ of the Casimir element, which in the complete-intersection setting is the class of the Jacobian determinant. It is used in the construction of a dual basis together with a Jacobian-determinant trace formula for an algebra given by a square presentation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_trace_eq_dual_lmul_of_bijective_rTensor.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.trace_eq_dual_lmul_of_bijective_rTensor
    (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A] [Module.Finite R A] [Module.Free R A]
    (τ : Module.Dual R A) (Δ : A ⊗[R] A)
    (hbal : ∀ s : A, (s ⊗ₜ[R] (1 : A)) * Δ = ((1 : A) ⊗ₜ[R] s) * Δ)
    (hbij : Function.Bijective (fun φ : Module.Dual R A => TensorProduct.lid R A (LinearMap.rTensor A φ Δ)))
    (hτ : TensorProduct.lid R A (LinearMap.rTensor A τ Δ) = 1) (x : A) :
    Algebra.trace R A x = τ (LinearMap.mul' R A Δ * x) := by sorry
