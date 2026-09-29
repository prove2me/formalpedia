-- Prove2me | Theorems.Thm_AutomorphicForm_existsUnique_mul_eq_mul_map_and_mulVec_eq_of_forall_ne_scalar_of_finrank_eq_two
-- name    : AutomorphicForm.existsUnique_mul_eq_mul_map_and_mulVec_eq_of_forall_ne_scalar_of_finrank_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/7031582b-d1d1-5897-ac25-4195d533cbb3
-- title:
--   Twisted commutant acts simply transitively on L²
-- statement:
--   Let $K$ be a field of characteristic zero and $L$ a field that is a $K$-algebra with $\dim_K L = 2$, and let $\sigma : L \to L$ be a $K$-algebra automorphism such that every $K$-algebra automorphism $\tau$ of $L$ lies in the subgroup of integer powers of $\sigma$. Let $\delta_0 \in \mathrm{GL}_2(L)$ be such that, for some $z \in L^\times$, $\delta_0 \cdot \sigma(\delta_0) = z \cdot 1$, where $\sigma$ acts on matrices entry by entry and $z \cdot 1$ denotes the scalar matrix; assume moreover that $x^{-1}\,\delta_0\,\sigma(x)$ is a scalar matrix $z \cdot 1$ for no $x \in \mathrm{GL}_2(L)$ and no $z \in L^\times$. Then for every nonzero column vector $v \in L^2$ and every column vector $w \in L^2$ there is exactly one matrix $x \in M_2(L)$ satisfying both $x\,\delta_0 = \delta_0\,\sigma(x)$ and $x v = w$. Thus, on the twisted commutant $D = \{x \in M_2(L) : x\delta_0 = \delta_0 \sigma(x)\}$, the evaluation map $x \mapsto x v$ is a bijection onto $L^2$ for each $v \neq 0$.
--
--   The set $D = \{x \in M_2(L) : x\delta_0 = \delta_0\sigma(x)\}$ attached to a $\sigma$-class $\delta_0$ with scalar norm that is not $\sigma$-conjugate to a scalar is a four-dimensional division algebra over $K$, and the present statement is the simple transitivity of its evaluation action on $L^2$: each nonzero $v$ gives a bijection $D \to L^2$, $x \mapsto xv$. It is used in the analysis of such twisted commutants, in particular in the computation of determinants of their elements, in the description of lattice conditions over the adelic completions, and in the compactness statement for elements of prescribed idele norm.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_existsUnique_mul_eq_mul_map_and_mulVec_eq_of_forall_ne_scalar_of_finrank_eq_two.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AutomorphicForm.existsUnique_mul_eq_mul_map_and_mulVec_eq_of_forall_ne_scalar_of_finrank_eq_two
    (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ₀ : GL (Fin 2) L)
    (hN : ∃ z : Lˣ, δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀ =
      Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ),
      x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠
        Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    (v : Fin 2 → L) (hv : v ≠ 0) (w : Fin 2 → L) :
    ∃! x : Matrix (Fin 2) (Fin 2) L,
      x * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * x.map σ ∧
        Matrix.mulVec x v = w := by sorry
