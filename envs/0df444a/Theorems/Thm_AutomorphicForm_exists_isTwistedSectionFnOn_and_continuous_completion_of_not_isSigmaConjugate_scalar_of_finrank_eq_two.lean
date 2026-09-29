-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_completion_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
-- name    : AutomorphicForm.exists_isTwistedSectionFnOn_and_continuous_completion_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/f046e558-9e96-5ef1-86d1-6df92f9a767b
-- title:
--   Continuous twisted section at a non-σ-conjugate scalar datum
-- statement:
--   Let $K \subseteq L$ be number fields with $[L:K] = 2$, let $\sigma$ be a $K$-algebra automorphism of $L$ such that every $K$-algebra automorphism of $L$ is an integral power of $\sigma$, let $v$ be an infinite place of $K$ with completion $K_v$, and write $\sigma$ also for the automorphism $\sigma \otimes \mathrm{id}$ of $L \otimes_K K_v$ and for its entrywise action on $\mathrm{GL}_2(L \otimes_K K_v)$. Let $c \in K_v^\times$ and let $\delta, y \in \mathrm{GL}_2(L \otimes_K K_v)$ satisfy the norm-conjugator relation: the image of the scalar matrix $c \cdot 1$ under the map induced by $K_v \to L \otimes_K K_v$ equals $y^{-1}\,\bigl(\delta \cdot \sigma(\delta)\bigr)\,y$, the product being the norm string $\prod_{i<[L:K]} \sigma^{i}(\delta)$. Assume further that $\delta$ is not $\sigma$-conjugate to any scalar, i.e. for no unit $z$ of $L \otimes_K K_v$ is there $x$ with $z \cdot 1 = x^{-1}\,\delta\,\sigma(x)$. Let $\tau'$ be a Haar measure on the twisted centraliser $T' = \{t \in \mathrm{GL}_2(L \otimes_K K_v) : t\,\delta\,\sigma(t)^{-1} = \delta\}$, taken with its Borel $\sigma$-algebra, and let $\varphi : \mathrm{GL}_2(L \otimes_K K_v) \to \mathbb{C}$ be continuous with compact support. Then there is a continuous $W : \mathrm{GL}_2(L \otimes_K K_v) \to \mathbb{R}$ which is everywhere non-negative, Borel measurable, of compact support, and satisfies $\int_{T'} W(tx)\,\mathrm{d}\tau'(t) = 1$ for every $x$ with $\varphi\bigl(x^{-1}\,\delta\,\sigma(x)\bigr) \neq 0$.
--
--   This provides the twisted section function needed to normalise twisted orbital integrals at an archimedean place in the case of the second kind, where the twisted norm of $\delta$ is central but $\delta$ itself is not $\sigma$-conjugate to a scalar; there the twisted centraliser is compact modulo a central split part. It is used in the archimedean comparison of a twisted orbital integral with an ordinary orbital integral at a scalar element, [`AutomorphicForm.twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom`](thm.html#AutomorphicForm.twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_completion_of_not_isSigmaConjugate_scalar_of_finrank_eq_two.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_isTwistedSectionFnOn_and_continuous_completion_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : InfinitePlace K) (c : (v.Completion)ˣ)
    (δ y : GL (Fin 2) (L ⊗[K] v.Completion))
    (hδ : IsNormConjugator K L v.Completion σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)
    (hδq : ∀ z : (L ⊗[K] v.Completion)ˣ,
      ¬ IsSigmaConjugate K L v.Completion σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z))
    (τ' : @Measure (twistedCentralizer K L v.Completion σ δ) (twistedCentralizerBorel K L v.Completion σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L v.Completion σ δ) τ')
    (φ : GL (Fin 2) (L ⊗[K] v.Completion) → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    ∃ W : GL (Fin 2) (L ⊗[K] v.Completion) → ℝ,
      IsTwistedSectionFnOn K L v.Completion σ δ τ' φ W ∧ Continuous W := by sorry
