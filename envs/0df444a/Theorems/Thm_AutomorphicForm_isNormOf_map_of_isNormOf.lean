-- Prove2me | Theorems.Thm_AutomorphicForm_isNormOf_map_of_isNormOf
-- name    : AutomorphicForm.isNormOf_map_of_isNormOf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/783ff332-c9c7-5dbe-9538-42cdd0e34561
-- title:
--   Norms in GL₂ are preserved by coefficient homomorphisms
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra (no finiteness of $L/K$ is assumed), let $A$ and $B$ be commutative rings that are $K$-algebras, let $g \colon A \to B$ be a homomorphism of $K$-algebras, and let $\sigma$ be a $K$-algebra automorphism of $L$. Let $\gamma \in GL_2(A)$ and $\delta \in GL_2(L \otimes_K A)$. The hypothesis is [`AutomorphicForm.IsNormOf K L A σ γ δ`](def/AutomorphicForm_TwistedOrbital.html#L217), i.e. there exists $y \in GL_2(L \otimes_K A)$ with $$\mathrm{toTensorGL}(\gamma) = y^{-1} \cdot \mathrm{normString}_{K,L,A,\sigma}(\delta) \cdot y,$$ where [`AutomorphicForm.toTensorGL`](def/AutomorphicForm_TwistedOrbital.html#L71) is the base-change map $GL_2(A) \to GL_2(L \otimes_K A)$ (entrywise $a \mapsto 1 \otimes a$) and [`AutomorphicForm.normString`](def/AutomorphicForm_TwistedOrbital.html#L205) is the twisted norm product of $\delta$ formed from the iterates of the entrywise action [`AutomorphicForm.sigmaGL`](def/AutomorphicForm_TwistedOrbital.html#L202) of $\sigma$ on the left tensor factor. The conclusion is the same predicate over $B$: the image of $\gamma$ under the entrywise map $GL_2(A) \to GL_2(B)$ induced by $g$ is a norm, in this sense, of the image of $\delta$ under the entrywise map induced by $\mathrm{id}_L \otimes g \colon L \otimes_K A \to L \otimes_K B$.
--
--   This is the functoriality in the coefficient algebra of the twisted norm relation of Langlands' base change for $GL(2)$: being a norm is preserved by any $K$-algebra homomorphism of coefficients, so that a global norm relation over an adele algebra restricts to norm relations over its local factors. It is used in the local analysis of twisted orbital integrals and of the twisted commutant, and in the factorisation of integrals of twisted elliptic folds.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isNormOf_map_of_isNormOf.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem AutomorphicForm.isNormOf_map_of_isNormOf
    (K L : Type) [Field K] [Field L] [Algebra K L]
    (A B : Type) [CommRing A] [Algebra K A] [CommRing B] [Algebra K B] (g : A →ₐ[K] B)
    (σ : L ≃ₐ[K] L) (γ : GL (Fin 2) A) (δ : GL (Fin 2) (L ⊗[K] A))
    (h : AutomorphicForm.IsNormOf K L A σ γ δ) :
    AutomorphicForm.IsNormOf K L B σ (Matrix.GeneralLinearGroup.map g.toRingHom γ)
      (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.map (AlgHom.id K L) g).toRingHom δ) := by sorry
