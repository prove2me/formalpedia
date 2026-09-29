-- Prove2me | Theorems.Thm_AutomorphicForm_exists_mul_sigmaTensor_eq_includeRight_inv_mul_of_forall_ne_of_finrank_eq_two
-- name    : AutomorphicForm.exists_mul_sigmaTensor_eq_includeRight_inv_mul_of_forall_ne_of_finrank_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/2b00766e-7f69-5860-aeb1-6623a0eda698
-- title:
--   Local norm index at most two for a quadratic extension
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra of degree $\mathrm{finrank}_K L = 2$, and let $\sigma$ be a $K$-algebra automorphism of $L$ such that every $K$-algebra automorphism $\tau$ of $L$ lies in the subgroup of integer powers of $\sigma$. Let $v$ be a height one prime of the ring of integers $\mathcal{O}_K$, with adic completion $K_v$, and let $s, s'$ be units of $K_v$. Write $\mathrm{sigmaTensor}$ for the ring endomorphism $\sigma \otimes \mathrm{id}$ of $L \otimes_K K_v$ obtained from $\sigma$ on the left factor and the identity on $K_v$, and write $a \mapsto 1 \otimes a$ for the right inclusion $K_v \to L \otimes_K K_v$ of algebras over $K$. Assume that no element $e$ of $L \otimes_K K_v$ satisfies $e \cdot (\sigma \otimes \mathrm{id})(e) = 1 \otimes s$, and likewise that no element $e$ satisfies $e \cdot (\sigma \otimes \mathrm{id})(e) = 1 \otimes s'$. Then there exists $e \in L \otimes_K K_v$ with $e \cdot (\sigma \otimes \mathrm{id})(e) = 1 \otimes (s^{-1} s')$, the element $s^{-1}s'$ of $K_v$ being the image of the corresponding unit.
--
--   This is the local norm index inequality for a quadratic extension, in the form that the elements of $K_v^\times$ of the shape $e\,\sigma(e)$ with $e$ in the semi-local algebra $L \otimes_K K_v$ form a subgroup of index at most $2$: if $s$ and $s'$ are both not of this shape, their quotient is. It is used in the construction of elements of a twisted centraliser with prescribed valuation and determinant, itself part of the comparison of automorphic forms under a quadratic base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_mul_sigmaTensor_eq_includeRight_inv_mul_of_forall_ne_of_finrank_eq_two.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_mul_sigmaTensor_eq_includeRight_inv_mul_of_forall_ne_of_finrank_eq_two
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (s s' : (v.adicCompletion K)ˣ)
    (hs : ∀ e : L ⊗[K] v.adicCompletion K,
      e * AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ e ≠
        (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) s)
    (hs' : ∀ e : L ⊗[K] v.adicCompletion K,
      e * AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ e ≠
        (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) s') :
    ∃ e : L ⊗[K] v.adicCompletion K,
      e * AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ e =
        (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K)
          ((s⁻¹ * s' : (v.adicCompletion K)ˣ) : v.adicCompletion K) := by sorry
