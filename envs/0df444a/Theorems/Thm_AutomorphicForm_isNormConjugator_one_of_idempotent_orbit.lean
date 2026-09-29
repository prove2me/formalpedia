-- Prove2me | Theorems.Thm_AutomorphicForm_isNormConjugator_one_of_idempotent_orbit
-- name    : AutomorphicForm.isNormConjugator_one_of_idempotent_orbit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/a3f0a1da-3459-55f5-98cc-ece496946fc0
-- title:
--   Every class is a norm with trivial conjugator
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra, let $A$ be a commutative $K$-algebra, and let $\sigma$ be a $K$-algebra automorphism of $L$. Write $n = \mathrm{finrank}_K L$ and let $\sigma$ act on $L \otimes_K A$ through `sigmaTensor K L A σ`, the ring homomorphism $\sigma \otimes \mathrm{id}_A$. Assume given $e \in L \otimes_K A$ with $e^2 = e$, such that $e \cdot (\sigma\otimes\mathrm{id})^{i}(e) = 0$ for all $i$ with $0 < i < n$, and such that $\sum_{i=0}^{n-1} (\sigma\otimes\mathrm{id})^{i}(e) = 1$. Then for every $\gamma \in GL_2(A)$ there exists $\delta \in GL_2(L \otimes_K A)$ with `IsNormConjugator K L A σ γ δ 1`, that is, the image of $\gamma$ under the homomorphism $GL_2(A) \to GL_2(L \otimes_K A)$ induced by $a \mapsto 1 \otimes a$ equals $1^{-1} \cdot \bigl(\prod_{i=0}^{n-1} (\mathrm{sigmaGL}\,K\,L\,A\,\sigma)^{i}(\delta)\bigr) \cdot 1$, the ordered product of the $\sigma$-translates of $\delta$ for $i = 0, \dots, n-1$ in $GL_2(L\otimes_K A)$. Finite-dimensionality of $L$ over $K$ is not assumed; the degree enters only through the numerical value $\mathrm{finrank}_K L$ occurring in the hypotheses and in the norm string.
--
--   This is the split case of the statement that every conjugacy class is a norm in cyclic base change for $GL(2)$: when $L \otimes_K A$ decomposes into factors cyclically permuted by $\sigma$, the idempotent $e$ cutting out one factor satisfies the hypotheses above, and every $\gamma \in GL_2(A)$ is then a norm with conjugator $1$. It is used in [`AutomorphicForm.exists_isNormOf_of_not_isSquare_discr_of_finrank_dvd_of_ramificationIdx_eq_one`](thm.html#AutomorphicForm.exists_isNormOf_of_not_isSquare_discr_of_finrank_dvd_of_ramificationIdx_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isNormConjugator_one_of_idempotent_orbit.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem AutomorphicForm.isNormConjugator_one_of_idempotent_orbit
    (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
    (σ : L ≃ₐ[K] L)
    (e : L ⊗[K] A) (he : IsIdempotentElem e)
    (horth : ∀ i, 0 < i → i < Module.finrank K L → e * (⇑(sigmaTensor K L A σ))^[i] e = 0)
    (hsum : (∑ i ∈ Finset.range (Module.finrank K L), (⇑(sigmaTensor K L A σ))^[i] e) = 1)
    (γ : GL (Fin 2) A) :
    ∃ δ : GL (Fin 2) (L ⊗[K] A), IsNormConjugator K L A σ γ δ 1 := by sorry
