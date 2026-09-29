-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isTwistedOrbitalIntegral_of_isRegularSemisimple_normString_of_isSemiLocalTestFn
-- name    : AutomorphicForm.exists_isTwistedOrbitalIntegral_of_isRegularSemisimple_normString_of_isSemiLocalTestFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/14398d74-efd0-51dc-9600-e33a2b136ec3
-- title:
--   Existence of twisted orbital integrals at regular semisimple norms
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $v$ be a nonzero prime of the ring of integers $\mathcal{O}_K$ with completion $K_v$, and let $\sigma$ be a $K$-algebra automorphism of $L$; write $n = [L:K]$ and let $\sigma$ act on $\mathrm{GL}_2(L \otimes_K K_v)$ entrywise through $\sigma \otimes \mathrm{id}$, this map being [`AutomorphicForm.sigmaGL`](def/AutomorphicForm_TwistedOrbital.html#L202). Let $\delta \in \mathrm{GL}_2(L \otimes_K K_v)$ be such that its norm string $\delta \cdot \sigma(\delta) \cdots \sigma^{n-1}(\delta)$ (the ordered product over $i \in \{0,\dots,n-1\}$ of $\sigma^{i}(\delta)$) is regular semisimple in the sense that $(\mathrm{tr})^2 - 4\det$ of that product is a unit of $L \otimes_K K_v$. Let $\tau'$ be a Haar measure, for the Borel $\sigma$-algebra, on the $\sigma$-twisted centralizer $\{t : t\,\delta\,\sigma(t)^{-1} = \delta\}$ of $\delta$, and let $\varphi_v : \mathrm{GL}_2(L \otimes_K K_v) \to \mathbb{C}$ be locally constant with compact support. Then there is a complex number $I'$ which is a twisted orbital integral of $\varphi_v$ at $\delta$ against $\tau'$: there exists $w : \mathrm{GL}_2(L \otimes_K K_v) \to \mathbb{R}$ satisfying the predicate [`AutomorphicForm.IsTwistedSectionFnOn`](def/AutomorphicForm_TwistedOrbital.html#L278) for the data $(\sigma, \delta, \tau', \varphi_v)$ with $$I' = \int \varphi_v\bigl(x^{-1}\delta\,\sigma(x)\bigr)\,w(x)\,d\mu(x),$$ the integral being taken against [`AutomorphicForm.semiLocalHaar K L v`](def/AutomorphicForm_TwistedOrbital.html#L169), the Haar measure on $\mathrm{GL}_2(L \otimes_K K_v)$ normalised to give the compact set [`AutomorphicForm.semiLocalIntegralCompacts K L v`](def/AutomorphicForm_TwistedOrbital.html#L154) volume one.
--
--   This is the existence of the $\sigma$-twisted orbital integral at a $\delta$ whose norm is regular semisimple, in the form used in base change for $\mathrm{GL}(2)$: the substance is the production of the weight function $w$, which rests on the fact that the set of $x$ with $x^{-1}\delta\,\sigma(x)$ in a given compact set is compact modulo the twisted centralizer. It is cited in the comparison of twisted orbital integrals with orbital integrals at the norm, in the matching statements for local test functions, and in the explicit computation at places with ramification index one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isTwistedOrbitalIntegral_of_isRegularSemisimple_normString_of_isSemiLocalTestFn.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory TopologicalSpace TensorProduct
open scoped TensorProduct.RightActions

theorem AutomorphicForm.exists_isTwistedOrbitalIntegral_of_isRegularSemisimple_normString_of_isSemiLocalTestFn
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (v.adicCompletion K) σ δ))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    [@Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ']
    (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφv : AutomorphicForm.IsSemiLocalTestFn K L v φv) :
    ∃ I' : ℂ, AutomorphicForm.IsTwistedOrbitalIntegral K L v σ δ τ' φv I' := by sorry
