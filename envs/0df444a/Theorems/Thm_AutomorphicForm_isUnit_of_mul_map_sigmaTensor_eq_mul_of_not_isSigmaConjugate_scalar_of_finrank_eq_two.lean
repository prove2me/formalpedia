-- Prove2me | Theorems.Thm_AutomorphicForm_isUnit_of_mul_map_sigmaTensor_eq_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
-- name    : AutomorphicForm.isUnit_of_mul_map_sigmaTensor_eq_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/b8c9cf1c-a08c-5289-97b3-4d2b326c73e6
-- title:
--   Invertibility of nonzero y with δ σ(y)∈ y M₂
-- statement:
--   Let $K$ be a field of characteristic zero and $L$ a $K$-algebra which is a field with $\dim_K L = 2$, let $\sigma$ be a $K$-algebra automorphism of $L$, and assume every $K$-algebra automorphism of $L$ lies in the subgroup of integer powers of $\sigma$. Let $A$ be a field which is a $K$-algebra, put $E = L \otimes_K A$, and let $\sigma$ act on $E$ by the ring homomorphism [`AutomorphicForm.sigmaTensor K L A σ`](def/AutomorphicForm_TwistedOrbital.html#L199) $= \sigma \otimes \mathrm{id}_A$, hence entrywise on $M_2(E)$ and on $\mathrm{GL}_2(E)$. Let $c \in A^\times$ and $\delta \in \mathrm{GL}_2(E)$ be such that the scalar matrix with diagonal entries $c$ is a norm of $\delta$ in the sense of [`AutomorphicForm.IsNormOf`](def/AutomorphicForm_TwistedOrbital.html#L217), i.e. there is $y_0 \in \mathrm{GL}_2(E)$ with $\mathrm{toTensorGL}\,K\,L\,A$ of that scalar matrix equal to $y_0^{-1}\cdot(\mathrm{normString}\,K\,L\,A\,\sigma\,\delta)\cdot y_0$, and such that for no $z \in E^\times$ is the scalar matrix $z\cdot 1$ of the form $x^{-1}\,\delta\,\sigma(x)$ with $x \in \mathrm{GL}_2(E)$. Then for all $y, k \in M_2(E)$ with $y \neq 0$ and $\delta \cdot \sigma(y) = y\cdot k$, the matrix $y$ is a unit of $M_2(E)$.
--
--   This is the ellipticity statement for a twisted conjugacy class: for a $\sigma$-conjugacy class with central norm containing no scalar matrix, the $\sigma$-semilinear operator $w \mapsto \delta\,\sigma(w)$ on $E^2$ stabilises no line, so any nonzero $y$ whose column space is $\Phi_\delta$-stable must be invertible. It is used in the analysis of twisted centralisers and twisted orbital integrals for $\mathrm{GL}_2$ over a quadratic extension, for instance by [`AutomorphicForm.existsUnique_mul_eq_mul_map_and_mulVec_eq_of_forall_ne_scalar_of_finrank_eq_two`](thm.html#AutomorphicForm.existsUnique_mul_eq_mul_map_and_mulVec_eq_of_forall_ne_scalar_of_finrank_eq_two) and [`AutomorphicForm.exists_isCompact_forall_twistedCentralizer_eq_scalar_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two`](thm.html#AutomorphicForm.exists_isCompact_forall_twistedCentralizer_eq_scalar_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isUnit_of_mul_map_sigmaTensor_eq_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem AutomorphicForm.isUnit_of_mul_map_sigmaTensor_eq_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
    (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (A : Type) [Field A] [Algebra K A]
    (c : Aˣ) (δ : GL (Fin 2) (L ⊗[K] A))
    (hδ : AutomorphicForm.IsNormOf K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ)
    (hδq : ∀ z : (L ⊗[K] A)ˣ,
      ¬ AutomorphicForm.IsSigmaConjugate K L A σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z))
    (y : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) (hy : y ≠ 0)
    (k : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))
    (hyk : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) * y.map (AutomorphicForm.sigmaTensor K L A σ) =
      y * k) :
    IsUnit y := by sorry
