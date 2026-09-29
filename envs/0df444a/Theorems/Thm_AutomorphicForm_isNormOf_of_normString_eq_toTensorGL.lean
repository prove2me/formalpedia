-- Prove2me | Theorems.Thm_AutomorphicForm_isNormOf_of_normString_eq_toTensorGL
-- name    : AutomorphicForm.isNormOf_of_normString_eq_toTensorGL
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/7a6c6922-b7ad-5381-888f-81fbd7016c4d
-- title:
--   Norm string equal to the base matrix implies norm
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra, let $A$ be a commutative ring that is a $K$-algebra, and let $\sigma$ be a $K$-algebra automorphism of $L$. Let $\gamma \in \mathrm{GL}_2(A)$ and $\varepsilon \in \mathrm{GL}_2(L \otimes_K A)$. Write $\iota$ for the group homomorphism [`AutomorphicForm.toTensorGL`](def/AutomorphicForm_TwistedOrbital.html#L71) $\colon \mathrm{GL}_2(A) \to \mathrm{GL}_2(L \otimes_K A)$ obtained by applying the algebra map $\mathrm{Algebra.TensorProduct.includeRight} \colon A \to L \otimes_K A$ entrywise, and write $N(\varepsilon)$ for [`AutomorphicForm.normString`](def/AutomorphicForm_TwistedOrbital.html#L205) $K\,L\,A\,\sigma\,\varepsilon$, the ordered product $\prod_{i=0}^{n-1} \tau^{i}(\varepsilon)$ over $i$ in `List.range` $n$ with $n = \operatorname{finrank}_K L$, where $\tau$ is the automorphism of $\mathrm{GL}_2(L \otimes_K A)$ induced entrywise by `sigmaTensor` $K\,L\,A\,\sigma$. The hypothesis is the equality $N(\varepsilon) = \iota(\gamma)$. The conclusion is [`AutomorphicForm.IsNormOf`](def/AutomorphicForm_TwistedOrbital.html#L217) $K\,L\,A\,\sigma\,\gamma\,\varepsilon$: there exists $y \in \mathrm{GL}_2(L \otimes_K A)$ with $\iota(\gamma) = y^{-1} \, N(\varepsilon) \, y$, i.e. $\gamma$ is a norm of $\varepsilon$ in the twisted-orbital sense.
--
--   This records the degenerate case of the relation ‘$\gamma$ is a norm of $\varepsilon$’ used in the twisted-orbital vocabulary: an $\varepsilon$ whose string of $\sigma$-twists multiplies exactly to $\gamma$ qualifies, no conjugation being needed. It serves as the interface through which elements produced inside a commutative subalgebra (so that the twisted product is computed directly) are fed into the norm predicate, and it is used in the analysis of the twisted commutant at a place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isNormOf_of_normString_eq_toTensorGL.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem AutomorphicForm.isNormOf_of_normString_eq_toTensorGL
    (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
    (σ : L ≃ₐ[K] L) (γ : GL (Fin 2) A) (ε : GL (Fin 2) (L ⊗[K] A))
    (h : AutomorphicForm.normString K L A σ ε = AutomorphicForm.toTensorGL K L A γ) :
    AutomorphicForm.IsNormOf K L A σ γ ε := by sorry
