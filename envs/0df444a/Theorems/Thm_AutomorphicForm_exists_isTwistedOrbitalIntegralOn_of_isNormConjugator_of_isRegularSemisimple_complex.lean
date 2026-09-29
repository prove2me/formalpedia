-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isTwistedOrbitalIntegralOn_of_isNormConjugator_of_isRegularSemisimple_complex
-- name    : AutomorphicForm.exists_isTwistedOrbitalIntegralOn_of_isNormConjugator_of_isRegularSemisimple_complex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/f7a28be9-b8fe-5008-8353-fe4ba8cd7d30
-- title:
--   Existence of twisted orbital integrals over ℂ
-- statement:
--   Let $K$ and $L$ be fields with $L$ a finite-dimensional $K$-algebra whose degree $n = \operatorname{finrank}_K L$ is prime, and let $\sigma$ be a $K$-algebra automorphism of $L$ with $\sigma \neq 1$. Fix a $K$-algebra structure on $\mathbb{C}$ and a $K$-algebra map $\iota : L \to \mathbb{C}$. Let $\mu_L$ be a Haar measure on $\mathrm{GL}_2(L \otimes_K \mathbb{C})$ for its Borel $\sigma$-algebra. Let $\gamma \in \mathrm{GL}_2(\mathbb{C})$ be regular semisimple in the sense that $\operatorname{tr}(\gamma)^2 - 4\det(\gamma)$ is a unit, and let $\delta, y \in \mathrm{GL}_2(L \otimes_K \mathbb{C})$ be such that $y$ conjugates the norm string of $\delta$ to $\gamma$: the image of $\gamma$ under the map induced by $a \mapsto 1 \otimes a$ equals $y^{-1} \bigl(\prod_{i=0}^{n-1} \sigma^i(\delta)\bigr) y$, where $\sigma$ acts on $\mathrm{GL}_2(L \otimes_K \mathbb{C})$ entrywise through the first tensor factor. Let $\tau'$ be a Haar measure, for the Borel $\sigma$-algebra, on the twisted centraliser $T'_\delta = \{t : t\,\delta\,\sigma(t)^{-1} = \delta\}$, and let $\varphi : \mathrm{GL}_2(L \otimes_K \mathbb{C}) \to \mathbb{C}$ be continuous with compact support. Then there is a complex number $I'$ and a function $w : \mathrm{GL}_2(L \otimes_K \mathbb{C}) \to \mathbb{R}$ that is non-negative, measurable and compactly supported, satisfies $\int_{T'_\delta} w(tx)\,\mathrm{d}\tau'(t) = 1$ for every $x$ with $\varphi(x^{-1}\delta\,\sigma(x)) \neq 0$, and for which $I' = \int \varphi(x^{-1}\delta\,\sigma(x))\,w(x)\,\mathrm{d}\mu_L(x)$.
--
--   This is the existence of the $\sigma$-twisted orbital integral of a continuous compactly supported test function at a $\sigma$-conjugacy class whose norm is regular semisimple, in the case of a place of $K$ split by the embedding $\iota$, so that the ambient group is $\mathrm{GL}_2(L \otimes_K \mathbb{C})$. It is used in the comparison of twisted orbital integrals on $\mathrm{GL}_2(L \otimes_K \mathbb{C})$ with ordinary orbital integrals on $\mathrm{GL}_2(\mathbb{C})$ that underlies the base-change identity at such a place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isTwistedOrbitalIntegralOn_of_isNormConjugator_of_isRegularSemisimple_complex.lean

import Definitions.Def_AutomorphicForm_SplitFibreIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions NNReal

theorem AutomorphicForm.exists_isTwistedOrbitalIntegralOn_of_isNormConjugator_of_isRegularSemisimple_complex
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    [Algebra K ℂ] (ι : L →ₐ[K] ℂ)
    (μL : @Measure (GL (Fin 2) (L ⊗[K] ℂ)) (glBorelOf (L ⊗[K] ℂ)))
    (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (L ⊗[K] ℂ)) μL)
    (γ : GL (Fin 2) ℂ) (hγ : IsRegularSemisimple γ)
    (δ y : GL (Fin 2) (L ⊗[K] ℂ)) (hy : IsNormConjugator K L ℂ σ γ δ y)
    (τ' : @Measure (twistedCentralizer K L ℂ σ δ) (twistedCentralizerBorel K L ℂ σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L ℂ σ δ) τ')
    (φ : GL (Fin 2) (L ⊗[K] ℂ) → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) :
    ∃ I' : ℂ, IsTwistedOrbitalIntegralOn K L ℂ σ μL δ τ' φ I' := by sorry
