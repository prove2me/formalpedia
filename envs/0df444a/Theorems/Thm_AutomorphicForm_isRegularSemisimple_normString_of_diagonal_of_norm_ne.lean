-- Prove2me | Theorems.Thm_AutomorphicForm_isRegularSemisimple_normString_of_diagonal_of_norm_ne
-- name    : AutomorphicForm.isRegularSemisimple_normString_of_diagonal_of_norm_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/7c5ddec2-1319-5a7a-8bcd-42d3cb8f40fd
-- title:
--   Diagonal δ with distinct entry norms has regular semisimple norm string
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a Galois extension of $K$, and let $\sigma$ be a $K$-algebra automorphism of $L$ whose integral powers exhaust $\mathrm{Gal}(L/K)$, i.e. every $\tau \in L \simeq_{\mathrm{alg}[K]} L$ lies in `Subgroup.zpowers σ`; thus $L/K$ is cyclic with generator $\sigma$. Let $v$ be a nonzero prime of the ring of integers $\mathcal{O}_K$, write $K_v$ for the associated completion `v.adicCompletion K`, and let $\delta \in \mathrm{GL}_2(L \otimes_K K_v)$ be an invertible matrix whose off-diagonal entries vanish, $\delta_{10} = \delta_{01} = 0$. Assume that the two diagonal entries have distinct norms, $\mathrm{Algebra.norm}_{K_v}(\delta_{00}) \neq \mathrm{Algebra.norm}_{K_v}(\delta_{11})$, the norm being taken for the $K_v$-algebra $L \otimes_K K_v$. The conclusion is that the norm string of $\delta$, namely the ordered product $\prod_{i=0}^{n-1} \sigma_i(\delta)$ with $n = \operatorname{finrank}_K L$ and $\sigma_i$ the $i$-fold iterate of the entrywise action `sigmaGL K L (v.adicCompletion K) σ` of $\sigma$ on the left tensor factor, is regular semisimple in the sense of the project: the element $(\operatorname{tr} M)^2 - 4 \det M$ of $L \otimes_K K_v$, for $M$ this product, is a unit.
--
--   This is the semi-local (at a single finite place $v$ of $K$) criterion identifying when a diagonal element of $\mathrm{GL}_2(L \otimes_K K_v)$ has regular semisimple norm string, the trace-squared-minus-four-determinant invariant being the square of the difference of the norms of the diagonal entries. It is the bridge from the diagonal, distinct-norm hypothesis to the regular semisimplicity required in the comparison of twisted orbital integrals, and it is used in [`AutomorphicForm.exists_forall_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_of_isSemiLocalTestFn`](thm.html#AutomorphicForm.exists_forall_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_of_isSemiLocalTestFn).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isRegularSemisimple_normString_of_diagonal_of_norm_ne.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct Pointwise
open scoped TensorProduct.RightActions

theorem AutomorphicForm.isRegularSemisimple_normString_of_diagonal_of_norm_ne
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K)) (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (h10 : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 0 = 0)
    (h01 : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 1 = 0)
    (hN : Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) ≠
        Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1)) :
    AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (v.adicCompletion K) σ δ) := by sorry
