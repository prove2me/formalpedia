-- Prove2me | Theorems.Thm_AutomorphicForm_isInvInvariant_twistedCentralizer_completion_of_isNormConjugator_scalar
-- name    : AutomorphicForm.isInvInvariant_twistedCentralizer_completion_of_isNormConjugator_scalar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/6b2e7d45-cce0-5296-a09c-5e0684f21de8
-- title:
--   Unimodularity of the local twisted centralizer of a scalar-norm δ
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, assume the degree $\operatorname{finrank}_K L$ is a prime number, and let $\sigma : L \simeq_{\mathrm{alg}[K]} L$ be such that every $K$-algebra automorphism $\tau$ of $L$ lies in the subgroup of integer powers of $\sigma$. Let $v$ be an infinite place of $K$, write $K_v$ for its completion, let $c \in K_v^{\times}$, and let $\delta, y \in \mathrm{GL}_2(L \otimes_K K_v)$ satisfy the relation `IsNormConjugator`: the image of the scalar matrix $c \cdot 1$ under the map $\mathrm{GL}_2(K_v) \to \mathrm{GL}_2(L \otimes_K K_v)$ induced by $a \mapsto 1 \otimes a$ equals $y^{-1} \left(\prod_{i=0}^{\ell-1} \sigma_{\mathrm{GL}}^{i}(\delta)\right) y$, where $\ell = \operatorname{finrank}_K L$ and $\sigma_{\mathrm{GL}}$ is the automorphism of $\mathrm{GL}_2(L \otimes_K K_v)$ induced entrywise by $\sigma \otimes \mathrm{id}$, the product being taken in the order $i = 0, 1, \dots, \ell-1$. Consider the twisted centralizer $T'_{\delta} = \{ t \in \mathrm{GL}_2(L \otimes_K K_v) \mid t \delta (\sigma_{\mathrm{GL}} t)^{-1} = \delta \}$, a subgroup equipped with its Borel $\sigma$-algebra for the subspace topology. Then every Haar measure $\tau'$ on $T'_{\delta}$ is invariant under inversion, i.e. its pushforward along $t \mapsto t^{-1}$ is $\tau'$ again.
--
--   This is the unimodularity of the $\sigma$-twisted centralizer of an element of $\mathrm{GL}_2(L \otimes_K K_v)$ whose twisted norm is conjugate to a central element, at a single archimedean place $v$; it is the ingredient needed to normalise Haar measures in twisted orbital integrals. It is cited by the corresponding statement over the infinite adele ring $\mathrm{GL}_2(L \otimes_K K_\infty)$, which is obtained from it place by place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isInvInvariant_twistedCentralizer_completion_of_isNormConjugator_scalar.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField AutomorphicForm
open scoped TensorProduct
open scoped TensorProduct.RightActions

theorem AutomorphicForm.isInvInvariant_twistedCentralizer_completion_of_isNormConjugator_scalar
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : InfinitePlace K) (c : (v.Completion)ˣ)
    (δ y : GL (Fin 2) (L ⊗[K] v.Completion))
    (hδ : AutomorphicForm.IsNormConjugator K L v.Completion σ
      (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L v.Completion σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L v.Completion σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L v.Completion σ δ) τ') :
    @Measure.IsInvInvariant _ (AutomorphicForm.twistedCentralizerBorel K L v.Completion σ δ) _ τ' := by sorry
