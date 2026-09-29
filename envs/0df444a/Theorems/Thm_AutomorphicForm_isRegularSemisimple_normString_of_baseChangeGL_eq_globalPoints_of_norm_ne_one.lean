-- Prove2me | Theorems.Thm_AutomorphicForm_isRegularSemisimple_normString_of_baseChangeGL_eq_globalPoints_of_norm_ne_one
-- name    : AutomorphicForm.isRegularSemisimple_normString_of_baseChangeGL_eq_globalPoints_of_norm_ne_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/97d4ff56-bbcc-5032-8a8b-d35a3f8bfc89
-- title:
--   Regular semisimplicity of the norm string of a diagonal global class
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a Galois extension of $K$, and let $\sigma$ be a $K$-automorphism of $L$ such that every $K$-automorphism of $L$ lies in the subgroup of integer powers of $\sigma$ (so $L/K$ is cyclic with $\sigma$ a generator). Let $t \in \mathrm{GL}_2(L)$ have vanishing off-diagonal entries, i.e. the $(1,0)$ and $(0,1)$ entries of the underlying matrix are $0$, and assume the diagonal entries satisfy $\mathrm{N}_{L/K}(t_{00}/t_{11}) \neq 1$, where $\mathrm{N}_{L/K}$ is the algebra norm of $L$ over $K$. Let $\delta \in \mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$, where $\mathbb{A}_K$ is the adele ring of $K$ formed from $\mathcal{O}_K$, and suppose that the entrywise image of $\delta$ under the ring isomorphism $L \otimes_K \mathbb{A}_K \cong \mathbb{A}_L$ of [`AutomorphicForm.baseChangeEquiv`](def/AutomorphicForm_BaseChangePlaces.html#L65) equals the image of $t$ under the map $\mathrm{GL}_2(L) \to \mathrm{GL}_2(\mathbb{A}_L)$ induced by the structure map $L \to \mathbb{A}_L$. Then the norm string $\prod_{i=0}^{n-1} \sigma^{i}(\delta)$, with $n = [L:K]$ and $\sigma$ acting entrywise through [`AutomorphicForm.sigmaGL`](def/AutomorphicForm_TwistedOrbital.html#L202), is regular semisimple in the sense of the project: writing $g$ for that product, $\mathrm{tr}(g)^2 - 4\det(g)$ is a unit of $L \otimes_K \mathbb{A}_K$.
--
--   This is the regularity input for the twisted orbital side of the base-change comparison: a diagonal global class whose diagonal ratio has norm different from $1$ has a norm string with invertible discriminant. It is used by the subsequent factorisation of twisted orbital integrals and by the statements computing Satake and winding data from them.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isRegularSemisimple_normString_of_baseChangeGL_eq_globalPoints_of_norm_ne_one.lean

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.isRegularSemisimple_normString_of_baseChangeGL_eq_globalPoints_of_norm_ne_one
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (t : GL (Fin 2) L) (ht₁ : (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (ht₂ : (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hreg : Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (hδ : AutomorphicForm.baseChangeGL K L δ = AutomorphicForm.globalPoints (𝓞 L) L t) :
    AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ δ) := by sorry
