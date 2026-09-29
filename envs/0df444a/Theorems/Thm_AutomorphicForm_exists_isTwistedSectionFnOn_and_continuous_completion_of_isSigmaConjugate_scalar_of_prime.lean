-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_completion_of_isSigmaConjugate_scalar_of_prime
-- name    : AutomorphicForm.exists_isTwistedSectionFnOn_and_continuous_completion_of_isSigmaConjugate_scalar_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/1ff3b9c8-b71c-577f-b0dc-170d63987f02
-- title:
--   Continuous twisted sections at a central class, archimedean place
-- statement:
--   Let $K$ and $L$ be number fields with $L/K$ a Galois extension whose degree $[L:K]=\operatorname{finrank}_K L$ is prime, and let $\sigma \in \mathrm{Gal}(L/K)$ be such that every element of $\mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$, i.e. $\sigma$ generates the Galois group. Let $v$ be an infinite place of $K$, with completion $K_v$, and put $A = L \otimes_K K_v$. Let $\delta \in \mathrm{GL}_2(A)$ and assume there is a unit $d \in A^\times$ such that the scalar matrix $d \cdot 1 \in \mathrm{GL}_2(A)$ is a $\sigma$-conjugate of $\delta$, that is $d\cdot 1 = x^{-1}\delta\,\sigma_{\mathrm{GL}}(x)$ for some $x \in \mathrm{GL}_2(A)$, where $\sigma_{\mathrm{GL}}$ is the automorphism of $\mathrm{GL}_2(A)$ induced entrywise by $\sigma \otimes \mathrm{id}$ on $A$. Let $T = \{t \in \mathrm{GL}_2(A) : t\,\delta\,\sigma_{\mathrm{GL}}(t)^{-1} = \delta\}$ be the $\sigma$-twisted centraliser of $\delta$, equipped with its Borel $\sigma$-algebra, and let $\tau'$ be a Haar measure on $T$ that is moreover invariant under inversion. Finally let $\varphi : \mathrm{GL}_2(A) \to \mathbb{C}$ have compact support (no continuity of $\varphi$ is assumed). Then there exists $W : \mathrm{GL}_2(A) \to \mathbb{R}$ which is continuous and is a twisted section function for these data: $W \geq 0$ everywhere, $W$ is Borel measurable, $W$ has compact support, and for every $x \in \mathrm{GL}_2(A)$ with $\varphi(x^{-1}\delta\,\sigma_{\mathrm{GL}}(x)) \neq 0$ one has $\int_T W(t x)\, d\tau'(t) = 1$.
--
--   This provides the normalising cut-off ("section") function used to unfold twisted orbital integrals at an archimedean place into integrals over the twisted conjugacy class of a central element, in the prime-degree cyclic situation. It is invoked in the archimedean comparison of twisted orbital integrals with ordinary orbital integrals at scalar classes and in the corresponding matching statement for transfer.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_completion_of_isSigmaConjugate_scalar_of_prime.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_isTwistedSectionFnOn_and_continuous_completion_of_isSigmaConjugate_scalar_of_prime
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (hprime : (Module.finrank K L).Prime)
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : InfinitePlace K)
    (δ : GL (Fin 2) (L ⊗[K] v.Completion))
    (hδ : ∃ d : (L ⊗[K] v.Completion)ˣ,
      IsSigmaConjugate K L v.Completion σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) d))
    (τ' : @Measure (twistedCentralizer K L v.Completion σ δ) (twistedCentralizerBorel K L v.Completion σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L v.Completion σ δ) τ')
    (hτ'i : @Measure.IsInvInvariant _ (twistedCentralizerBorel K L v.Completion σ δ) _ τ')
    (φ : GL (Fin 2) (L ⊗[K] v.Completion) → ℂ) (hφ : HasCompactSupport φ) :
    ∃ W : GL (Fin 2) (L ⊗[K] v.Completion) → ℝ,
      IsTwistedSectionFnOn K L v.Completion σ δ τ' φ W ∧ Continuous W := by sorry
