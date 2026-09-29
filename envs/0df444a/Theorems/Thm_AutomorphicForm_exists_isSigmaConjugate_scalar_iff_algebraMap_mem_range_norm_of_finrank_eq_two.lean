-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isSigmaConjugate_scalar_iff_algebraMap_mem_range_norm_of_finrank_eq_two
-- name    : AutomorphicForm.exists_isSigmaConjugate_scalar_iff_algebraMap_mem_range_norm_of_finrank_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/e0e4299a-ed2a-5cf0-b338-fa24968b4f92
-- title:
--   σ-conjugacy to a scalar versus norms from L⊗_KF
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra of degree $\operatorname{finrank}_K L = 2$, and let $\sigma$ be a $K$-algebra automorphism of $L$ such that every $K$-automorphism $\tau$ of $L$ lies in the subgroup of integer powers of $\sigma$. Let $F$ be a field equipped with a $K$-algebra structure (no finiteness or number-field hypothesis on $F$). Let $\delta_0 \in \mathrm{GL}_2(L)$ and $a \in K^\times$ satisfy $\delta_0 \cdot \sigma(\delta_0) = (\iota(a)) \cdot 1$, where $\sigma$ acts entrywise on matrices, $\iota$ is the structure map $K \to L$, and the right-hand side is the scalar matrix with diagonal entry the image of $a$ in $L^\times$. Write $\delta_0$ also for its image in $\mathrm{GL}_2(L \otimes_K F)$ under the entrywise application of $\ell \mapsto \ell \otimes 1$. The assertion is the equivalence of: (i) there is a unit $z$ of $L \otimes_K F$ and an $x \in \mathrm{GL}_2(L \otimes_K F)$ with $z \cdot 1 = x^{-1} \, \delta_0 \, (\sigma \otimes \mathrm{id})(x)$, the twist acting entrywise through the first tensor factor; and (ii) the image of $a$ in $F$ is $\mathrm{N}_{(L \otimes_K F)/F}(x)$ for some unit $x$ of $L \otimes_K F$.
--
--   This is the local dichotomy underlying twisted (σ-)conjugacy classes in base change for $\mathrm{GL}_2$ over a quadratic extension: an element whose norm string is a central element of $K^\times$ becomes σ-conjugate to a scalar over $L \otimes_K F$ exactly when that central element is a norm from $(L \otimes_K F)^\times$, the obstruction being a Hilbert-90 type computation for $\mathrm{GL}_2$ of the quadratic $F$-algebra $L \otimes_K F$. It is used by [`AutomorphicForm.finite_and_even_ncard_places_not_isSigmaConjugate_scalar_of_finrank_eq_two`](thm.html#AutomorphicForm.finite_and_even_ncard_places_not_isSigmaConjugate_scalar_of_finrank_eq_two), where the places at which the scalar class fails to be attained are counted.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isSigmaConjugate_scalar_iff_algebraMap_mem_range_norm_of_finrank_eq_two.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_isSigmaConjugate_scalar_iff_algebraMap_mem_range_norm_of_finrank_eq_two
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (F : Type) [Field F] [Algebra K F]
    (δ₀ : GL (Fin 2) L) (a : Kˣ)
    (ha : δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀ =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap K L : K →* L) a)) :
    (∃ z : (L ⊗[K] F)ˣ, AutomorphicForm.IsSigmaConjugate K L F σ
        (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] F) δ₀)
        (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) ↔
      algebraMap K F (a : K) ∈
        Set.range (fun x : (L ⊗[K] F)ˣ => Algebra.norm F (x : L ⊗[K] F)) := by sorry
