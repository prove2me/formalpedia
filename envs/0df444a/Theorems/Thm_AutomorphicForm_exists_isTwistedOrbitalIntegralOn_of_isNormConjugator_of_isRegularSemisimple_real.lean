-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isTwistedOrbitalIntegralOn_of_isNormConjugator_of_isRegularSemisimple_real
-- name    : AutomorphicForm.exists_isTwistedOrbitalIntegralOn_of_isNormConjugator_of_isRegularSemisimple_real
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/2eb84590-c8a6-5117-ad6b-9df43189e754
-- title:
--   Existence of twisted orbital integrals at a real place
-- statement:
--   Let $K \subseteq L$ be fields with $L$ finite-dimensional over $K$ of prime degree $n = \operatorname{finrank}_K L$, let $\sigma$ be a $K$-algebra automorphism of $L$ with $\sigma \neq 1$, let $\mathbb{R}$ carry a $K$-algebra structure, and let $\iota : L \to \mathbb{R}$ be a $K$-algebra map. Let $\mu_L$ be a Haar measure on $\mathrm{GL}_2(L \otimes_K \mathbb{R})$ for the Borel $\sigma$-algebra `glBorelOf`. Let $\gamma \in \mathrm{GL}_2(\mathbb{R})$ be regular semisimple in the sense that $\operatorname{tr}(\gamma)^2 - 4\det(\gamma)$ is a unit, and let $\delta, y \in \mathrm{GL}_2(L \otimes_K \mathbb{R})$ satisfy the norm-conjugacy relation: the image of $\gamma$ under the entrywise map induced by $a \mapsto 1 \otimes a$ equals $y^{-1} \bigl(\delta \cdot \sigma(\delta) \cdots \sigma^{n-1}(\delta)\bigr) y$, where $\sigma$ acts on $\mathrm{GL}_2(L \otimes_K \mathbb{R})$ entrywise through the first tensor factor. Let $\tau'$ be a Haar measure, for the Borel $\sigma$-algebra, on the twisted centralizer $T'_\delta = \{t : t\,\delta\,\sigma(t)^{-1} = \delta\}$, and let $\varphi : \mathrm{GL}_2(L \otimes_K \mathbb{R}) \to \mathbb{C}$ be continuous with compact support. Then there is a complex number $I'$ which is a twisted orbital integral of $\varphi$ at $\delta$: that is, there is $w : \mathrm{GL}_2(L \otimes_K \mathbb{R}) \to \mathbb{R}$ which is non-negative, measurable and compactly supported, satisfies $\int_{T'_\delta} w(tx)\,d\tau'(t) = 1$ for every $x$ with $\varphi(x^{-1}\delta\,\sigma(x)) \neq 0$, and for which $I' = \int \varphi(x^{-1}\delta\,\sigma(x))\,w(x)\,d\mu_L(x)$.
--
--   This is the existence half of the theory of $\sigma$-twisted orbital integrals for $\mathrm{GL}_2$ over a split (real) place, as they occur on the base-change side of the comparison of trace formulae: the unbounded volume of the twisted conjugacy class is regularised by a section function for the twisted centralizer, and the assertion is that some such regularised value exists. It feeds the comparison of a twisted orbital integral at $\delta$ with an ordinary orbital integral at the norm $\gamma$ in [`AutomorphicForm.isOrbitalIntegralOn_scalar_of_isTwistedOrbitalIntegralOn_of_algHom_real_of_nhds_forall_isRegularSemisimple`](thm.html#AutomorphicForm.isOrbitalIntegralOn_scalar_of_isTwistedOrbitalIntegralOn_of_algHom_real_of_nhds_forall_isRegularSemisimple).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isTwistedOrbitalIntegralOn_of_isNormConjugator_of_isRegularSemisimple_real.lean

import Definitions.Def_AutomorphicForm_SplitFibreIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions NNReal

theorem AutomorphicForm.exists_isTwistedOrbitalIntegralOn_of_isNormConjugator_of_isRegularSemisimple_real
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    [Algebra K ℝ] (ι : L →ₐ[K] ℝ)
    (μL : @Measure (GL (Fin 2) (L ⊗[K] ℝ)) (glBorelOf (L ⊗[K] ℝ)))
    (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (L ⊗[K] ℝ)) μL)
    (γ : GL (Fin 2) ℝ) (hγ : IsRegularSemisimple γ)
    (δ y : GL (Fin 2) (L ⊗[K] ℝ)) (hy : IsNormConjugator K L ℝ σ γ δ y)
    (τ' : @Measure (twistedCentralizer K L ℝ σ δ) (twistedCentralizerBorel K L ℝ σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L ℝ σ δ) τ')
    (φ : GL (Fin 2) (L ⊗[K] ℝ) → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) :
    ∃ I' : ℂ, IsTwistedOrbitalIntegralOn K L ℝ σ μL δ τ' φ I' := by sorry
