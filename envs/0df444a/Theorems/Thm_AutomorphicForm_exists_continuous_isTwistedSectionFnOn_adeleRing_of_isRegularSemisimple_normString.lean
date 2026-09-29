-- Prove2me | Theorems.Thm_AutomorphicForm_exists_continuous_isTwistedSectionFnOn_adeleRing_of_isRegularSemisimple_normString
-- name    : AutomorphicForm.exists_continuous_isTwistedSectionFnOn_adeleRing_of_isRegularSemisimple_normString
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/32619903-0eb5-5395-bdcd-b1513ca80854
-- title:
--   Continuous section functions for adelic twisted orbital integrals
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a finite extension of $K$ (as an algebra over $K$), let $\sigma$ be a $K$-algebra automorphism of $L$, and let $\delta$ be an element of $\mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$, where $\mathbb{A}_K$ is the adele ring of $K$ and $\sigma$ acts on $\mathrm{GL}_2(L\otimes_K \mathbb{A}_K)$ entrywise through $\sigma \otimes \mathrm{id}$, this action being written [`AutomorphicForm.sigmaGL`](def/AutomorphicForm_TwistedOrbital.html#L202). Assume the norm string $N(\delta) = \delta \cdot \sigma(\delta) \cdots \sigma^{n-1}(\delta)$, the product of the first $n = [L:K]$ iterates of $\sigma$ applied to $\delta$, is regular semisimple in the sense that $\mathrm{tr}(N(\delta))^2 - 4\det(N(\delta))$ is a unit of $L \otimes_K \mathbb{A}_K$. Let $\tau'$ be a measure on the twisted centraliser $\{t : t\delta\sigma(t)^{-1} = \delta\}$, equipped with its Borel $\sigma$-algebra, and assume $\tau'$ is a Haar measure. Let $\varphi : \mathrm{GL}_2(L\otimes_K\mathbb{A}_K) \to \mathbb{C}$ have compact support. Then there exists $w : \mathrm{GL}_2(L\otimes_K\mathbb{A}_K) \to \mathbb{R}$ which is continuous and satisfies `IsTwistedSectionFnOn`: $w \ge 0$ everywhere, $w$ is Borel measurable, $w$ has compact support, and for every $x$ with $\varphi(x^{-1}\delta\sigma(x)) \neq 0$ one has $\int w(tx)\,d\tau'(t) = 1$, the integral being over the twisted centraliser. No condition relating the order of $\sigma$ to $[L:K]$ is imposed.
--
--   This is the normalisation ("nice section function") step for twisted orbital integrals on $\mathrm{GL}_2$ over the adeles: a continuous, compactly supported weight that integrates to $1$ over the twisted centraliser along the twisted conjugacy class supporting $\varphi$, in the style of the section functions used in base change for $\mathrm{GL}(2)$. Continuity, and hence boundedness, of $w$ is what makes the Fubini manipulations licit in the subsequent unfolding of twisted orbital integrals over the centre and the kernel of the idelic norm.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_continuous_isTwistedSectionFnOn_adeleRing_of_isRegularSemisimple_normString.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_continuous_isTwistedSectionFnOn_adeleRing_of_isRegularSemisimple_normString
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
    ∃ w : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℝ, Continuous w ∧
      AutomorphicForm.IsTwistedSectionFnOn K L (AdeleRing (𝓞 K) K) σ δ τ' φ w := by sorry
