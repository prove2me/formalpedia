-- Prove2me | Theorems.Thm_AutomorphicForm_exists_linearMap_apply_eq_mul_sigmaTensor_sub_mul_and_det_eq_neg_one_pow_mul_norm_sub_norm_of_infinite
-- name    : AutomorphicForm.exists_linearMap_apply_eq_mul_sigmaTensor_sub_mul_and_det_eq_neg_one_pow_mul_norm_sub_norm_of_infinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/c6d179dd-0eca-57c9-855f-2c646a6260c7
-- title:
--   Determinant of y↦ aσ(y)-by on L⊗_K A
-- statement:
--   Let $K$ and $L$ be fields with $L$ a finite Galois extension of $K$, and assume $K$ is infinite. Let $\sigma$ be a $K$-algebra automorphism of $L$ such that every $K$-algebra automorphism $\tau$ of $L$ lies in the subgroup of integer powers of $\sigma$, so that $\mathrm{Gal}(L/K)$ is cyclic with generator $\sigma$. Let $A$ be a commutative ring equipped with a $K$-algebra structure, and let $a,b$ be elements of the ring $L\otimes_K A$, viewed as an $A$-algebra through its right-hand factor. Write $\sigma_A$ for [`AutomorphicForm.sigmaTensor K L A σ`](def/AutomorphicForm_TwistedOrbital.html#L199), the ring endomorphism of $L\otimes_K A$ obtained from the algebra map $\sigma\otimes\mathrm{id}_A$. The assertion is that there exists an $A$-linear endomorphism $T$ of $L\otimes_K A$ such that $T(y)=a\cdot\sigma_A(y)-b\cdot y$ for every $y\in L\otimes_K A$, and whose determinant is $$\det T=(-1)^{[L:K]}\bigl(N_{(L\otimes_K A)/A}(b)-N_{(L\otimes_K A)/A}(a)\bigr),$$ the norms being the $A$-algebra norms of $L\otimes_K A$ (determinants of multiplication), and $[L:K]$ the $K$-dimension of $L$.
--
--   This is the algebraic computation underlying the Jacobian of the twisted map $y\mapsto a\sigma(y)-by$ occurring in twisted orbital integrals for a cyclic extension, stated over an arbitrary commutative $K$-algebra base $A$ so that both the finite-place and the archimedean cases can use it. It is invoked in the evaluation of the additive Haar measure of such a map over the infinite adeles and in the corresponding change-of-variables formula for integrals; the proof reduces to the determinant of $\sigma-c\cdot\mathrm{id}$ on $L$ over $K$ via [`AlgEquiv.algebraMap_det_toLinearMap_sub_smul_id_eq_of_orderOf_eq_finrank`](thm.html#AlgEquiv.algebraMap_det_toLinearMap_sub_smul_id_eq_of_orderOf_eq_finrank).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_linearMap_apply_eq_mul_sigmaTensor_sub_mul_and_det_eq_neg_one_pow_mul_norm_sub_norm_of_infinite.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_linearMap_apply_eq_mul_sigmaTensor_sub_mul_and_det_eq_neg_one_pow_mul_norm_sub_norm_of_infinite
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Infinite K]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (A : Type) [CommRing A] [Algebra K A] (a b : L ⊗[K] A) :
    ∃ T : (L ⊗[K] A) →ₗ[A] (L ⊗[K] A),
      (∀ y : L ⊗[K] A, T y = a * AutomorphicForm.sigmaTensor K L A σ y - b * y) ∧
      LinearMap.det T = (-1) ^ Module.finrank K L * (Algebra.norm A b - Algebra.norm A a) := by sorry
