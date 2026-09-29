-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isTwistedSectionFnOn_adeleRing_of_isRegularSemisimple_normString
-- name    : AutomorphicForm.exists_isTwistedSectionFnOn_adeleRing_of_isRegularSemisimple_normString
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/fe61e613-4c09-557a-aa61-b30b2384d91b
-- title:
--   Twisted section functions exist at classes with regular semisimple norm
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a finite extension of $K$, let $\sigma$ be a $K$-algebra automorphism of $L$, and write $G' = \mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$, where $\mathbb{A}_K$ is the adele ring of $K$, with $\sigma$ acting on $G'$ entrywise through the automorphism $\sigma \otimes \mathrm{id}$ of $L \otimes_K \mathbb{A}_K$; this induced group homomorphism of $G'$ is [`AutomorphicForm.sigmaGL`](def/AutomorphicForm_TwistedOrbital.html#L202). Let $\delta \in G'$ and assume that its norm string $N\delta = \prod_{i=0}^{n-1} \sigma^i(\delta)$, $n = \operatorname{finrank}_K L$, taken in this order, is regular semisimple in the sense that $(\operatorname{tr} N\delta)^2 - 4 \det N\delta$ is a unit of $L \otimes_K \mathbb{A}_K$. Let $T' = \{t \in G' : t\,\delta\,\sigma(t)^{-1} = \delta\}$ be the $\sigma$-twisted centraliser of $\delta$, a subgroup of $G'$, equipped with the Borel $\sigma$-algebra of its subspace topology and with a Haar measure $\tau'$. Let $\varphi \colon G' \to \mathbb{C}$ have compact support. Then there exists $w \colon G' \to \mathbb{R}$ which is everywhere non-negative, Borel measurable for the Borel $\sigma$-algebra on $G'$ and compactly supported, and satisfies $\int_{T'} w(t x)\,d\tau'(t) = 1$ for every $x \in G'$ with $\varphi(x^{-1} \delta\, \sigma(x)) \neq 0$. No hypothesis relating $\sigma$ to a cyclic group of order $n$ is imposed in the statement.
--
--   This is the statement that adelic twisted orbital integrals of compactly supported functions converge at the twisted classes whose norm string is regular semisimple, packaged through a section function so that the integral over $T' \backslash G'$ can be written as an integral over $G'$ against $w$ without quotient measures. It is the twisted counterpart of the corresponding existence result for ordinary orbital integrals, and is used downstream in the analysis of $\sigma$-elliptic terms and of the matching of local and adelic orbital integrals for $\mathrm{GL}_2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isTwistedSectionFnOn_adeleRing_of_isRegularSemisimple_normString.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_isTwistedSectionFnOn_adeleRing_of_isRegularSemisimple_normString
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (σ : L ≃ₐ[K] L)
    (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ δ))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ) τ')
    (φ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ) (hφ : HasCompactSupport φ) :
    ∃ w : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℝ,
      AutomorphicForm.IsTwistedSectionFnOn K L (AdeleRing (𝓞 K) K) σ δ τ' φ w := by sorry
