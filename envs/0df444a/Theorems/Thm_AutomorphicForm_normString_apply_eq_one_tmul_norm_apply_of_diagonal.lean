-- Prove2me | Theorems.Thm_AutomorphicForm_normString_apply_eq_one_tmul_norm_apply_of_diagonal
-- name    : AutomorphicForm.normString_apply_eq_one_tmul_norm_apply_of_diagonal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/b5b52f0a-ba1a-565d-841d-9ef808bcd4bc
-- title:
--   Norm string of a diagonal matrix in base-changed GL₂
-- statement:
--   Let $K$ and $L$ be fields with $L$ a finite Galois extension of $K$, let $\sigma$ be a $K$-algebra automorphism of $L$, and assume that every $K$-algebra automorphism $\tau$ of $L$ lies in the subgroup of integer powers of $\sigma$, so that the Galois group is cyclic with generator $\sigma$. Let $A$ be a commutative $K$-algebra, and regard $E = L \otimes_K A$ as an $A$-algebra through its right factor. Let $\delta \in GL_2(E)$ be a matrix whose off-diagonal entries both vanish: $\delta_{10} = 0$ and $\delta_{01} = 0$. Write $\mathcal{N}\delta =$ [`AutomorphicForm.normString K L A σ δ`](def/AutomorphicForm_TwistedOrbital.html#L205) for the product $\prod_{i=0}^{[L:K]-1} (\mathrm{sigmaGL})^{i}(\delta)$, where `sigmaGL K L A σ` is the group endomorphism of $GL_2(E)$ obtained by applying the map `sigmaTensor K L A σ` of $E$ attached to $\sigma$ to each matrix entry, and the factors are taken in the order $i = 0, 1, \dots, [L:K]-1$. The conclusion is a fourfold conjunction: the $(1,0)$ and $(0,1)$ entries of $\mathcal{N}\delta$ vanish, the $(0,0)$ entry equals $1 \otimes_K \mathrm{N}_{E/A}(\delta_{00})$, and the $(1,1)$ entry equals $1 \otimes_K \mathrm{N}_{E/A}(\delta_{11})$, where $\mathrm{N}_{E/A}$ is the algebra norm of $E$ over $A$.
--
--   This is the computation of the norm map on split (diagonal) twisted classes in cyclic base change for $GL_2$: the norm string of $\mathrm{diag}(\alpha,\beta)$ over $L \otimes_K A$ is the diagonal matrix of the norms of $\alpha$ and $\beta$, pushed into $L \otimes_K A$. It is used in the comparison of twisted orbital integrals with orbital integrals on the base, in particular by the statements characterising which diagonal elements arise as norms and by the constructions of twisted torus families.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_normString_apply_eq_one_tmul_norm_apply_of_diagonal.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.normString_apply_eq_one_tmul_norm_apply_of_diagonal
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (A : Type) [CommRing A] [Algebra K A]
    (δ : GL (Fin 2) (L ⊗[K] A))
    (h10 : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0) (h01 : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0) :
    ((AutomorphicForm.normString K L A σ δ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0 ∧
    ((AutomorphicForm.normString K L A σ δ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0 ∧
    ((AutomorphicForm.normString K L A σ δ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0 =
      (1 : L) ⊗ₜ[K] Algebra.norm A ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0) ∧
    ((AutomorphicForm.normString K L A σ δ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1 =
      (1 : L) ⊗ₜ[K] Algebra.norm A ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1) := by sorry
