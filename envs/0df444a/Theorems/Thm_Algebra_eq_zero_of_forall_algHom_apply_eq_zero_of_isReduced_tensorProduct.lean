-- Prove2me | Theorems.Thm_Algebra_eq_zero_of_forall_algHom_apply_eq_zero_of_isReduced_tensorProduct
-- name    : Algebra.eq_zero_of_forall_algHom_apply_eq_zero_of_isReduced_tensorProduct
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/4e3ca798-da53-56f6-8255-3acb3b3ef659
-- title:
--   Points into an algebraically closed field separate elements
-- statement:
--   Let $R$ be a commutative ring which is a domain, and let $K$ be a field equipped with an $R$-algebra structure making it a fraction field of $R$. Let $B$ be a commutative $R$-algebra with no zero smul divisors over $R$, i.e. torsion-free in the sense that $r \cdot b = 0$ with $r \neq 0$ forces $b = 0$; assume that the generic fibre $K \otimes_R B$ is a reduced ring and is finite-dimensional as a $K$-module. Let $\Omega$ be an algebraically closed field which is an algebra over both $R$ and $K$, compatibly (a scalar tower $R \to K \to \Omega$). Then for $b \in B$, if $\varphi(b) = 0$ for every $R$-algebra homomorphism $\varphi : B \to \Omega$, one has $b = 0$. All of $R$, $K$, $B$, $\Omega$ live in a single universe $u$.
--
--   The statement expresses that the $\Omega$-valued points of such an $R$-algebra separate its elements; it is the separation input needed when comparing algebra maps out of $B$ through their values at geometric points. It is used in the project's treatment of finite flat Hopf orders and of Néron models of modular curves at a prime, for instance in identifying maps out of a base-changed group scheme by their effect on residue fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_eq_zero_of_forall_algHom_apply_eq_zero_of_isReduced_tensorProduct.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem Algebra.eq_zero_of_forall_algHom_apply_eq_zero_of_isReduced_tensorProduct
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {B : Type u} [CommRing B] [Algebra R B] [NoZeroSMulDivisors R B]
    [IsReduced (TensorProduct R K B)] [Module.Finite K (TensorProduct R K B)]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω] [Algebra K Ω] [IsScalarTower R K Ω]
    (b : B) (hb : ∀ φ : B →ₐ[R] Ω, φ b = 0) : b = 0 := by sorry
