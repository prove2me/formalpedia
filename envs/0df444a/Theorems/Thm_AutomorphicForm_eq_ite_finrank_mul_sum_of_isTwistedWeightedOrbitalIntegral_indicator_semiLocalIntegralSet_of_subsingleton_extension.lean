-- Prove2me | Theorems.Thm_AutomorphicForm_eq_ite_finrank_mul_sum_of_isTwistedWeightedOrbitalIntegral_indicator_semiLocalIntegralSet_of_subsingleton_extension
-- name    : AutomorphicForm.eq_ite_finrank_mul_sum_of_isTwistedWeightedOrbitalIntegral_indicator_semiLocalIntegralSet_of_subsingleton_extension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/78878882-5b07-5d28-a42b-b9194e162c79
-- title:
--   Twisted weighted orbital integral of the unit at an inert place
-- statement:
--   Let $K\subset L$ be number fields with $\ell=[L:K]$ prime, let $\sigma$ be a non-trivial $K$-automorphism of $L$, and let $v$ be a maximal ideal of $\mathcal O_K$ such that every maximal ideal $w$ of $\mathcal O_L$ lying under $v$ has ramification index $1$ over $v$ and such that the type of primes of $\mathcal O_L$ above $v$ is a subsingleton. Put $q=\mathrm{absNorm}\,v$. Let $a\neq b$ be units of the completion $K_v$ and $m\in\mathbb Z$ with $\|a-b\|=q^{-m}$, and let $\alpha,\beta$ be units of $L\otimes_K K_v$ such that the norm string $\prod_{i=0}^{\ell-1}\sigma_{\mathrm{GL}}^{i}(\mathrm{diag}(\alpha,\beta))$ of $\delta=\mathrm{diag}(\alpha,\beta)$, formed with the automorphism of $\mathrm{GL}_2(L\otimes_K K_v)$ induced by $\sigma\otimes 1$, equals the image of $\mathrm{diag}(a,b)$ under $\mathrm{GL}_2(K_v)\to\mathrm{GL}_2(L\otimes_K K_v)$. Let $\tau'$ be a Haar measure, for the Borel structure of the subspace topology, on the $\sigma$-twisted centraliser $\{t\mid t\delta\sigma(t)^{-1}=\delta\}$ of $\delta$, normalised so that the set of its elements whose underlying matrix and inverse matrix have all entries in the image of $\mathcal O_L\otimes\mathcal O_{K_v}$ has mass $1$. Finally let $J'\in\mathbb C$ be a $\sigma$-twisted weighted orbital integral of $\delta$ for the indicator function of that integral subset of $\mathrm{GL}_2(L\otimes_K K_v)$: there is a twisted section function $s$ for these data with $J'=\int \varphi(x^{-1}\delta\,\sigma_{\mathrm{GL}}(x))\,\mathrm{wt}(x)\,s(x)$ against the Haar measure of $\mathrm{GL}_2(L\otimes_K K_v)$ normalised on the integral points, the weight $\mathrm{wt}$ being the finite sum over the primes of $\mathcal O_L$ above $v$ of the local weights of the corresponding components of $x$. Then $J'=0$ unless $\|a\|=\|b\|=1$, in which case $$J'=\ell\cdot 2\log q\cdot\sum_{s=0}^{\max(m,0)} s\,(q^{s}-q^{s}/q),$$ the real number on the right being viewed in $\mathbb C$.
--
--   This is the twisted side, at an unramified place with a single prime above it, of the weighted fundamental lemma for the unit element of the Hecke algebra, in the form used in Langlands' base change for $\mathrm{GL}(2)$: the value is $[L:K]$ times the corresponding untwisted weighted orbital integral of $\mathrm{diag}(a,b)$. It is used by [`AutomorphicForm.twistedWeighted_eq_finrank_mul_weighted_indicator_of_unramified`](thm.html#AutomorphicForm.twistedWeighted_eq_finrank_mul_weighted_indicator_of_unramified).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_eq_ite_finrank_mul_sum_of_isTwistedWeightedOrbitalIntegral_indicator_semiLocalIntegralSet_of_subsingleton_extension.lean

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.eq_ite_finrank_mul_sum_of_isTwistedWeightedOrbitalIntegral_indicator_semiLocalIntegralSet_of_subsingleton_extension
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (hinert : Subsingleton (v.Extension (𝓞 L)))
    (a b : (v.adicCompletion K)ˣ) (hab : a ≠ b) (m : ℤ)
    (hm : ‖(a : v.adicCompletion K) - b‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-m))
    (α β : (L ⊗[K] v.adicCompletion K)ˣ)
    (hN : AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
      AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a b))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β))
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)))
    (hτ' : @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ')
    (hτ'1 : τ' {t | (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈
      AutomorphicForm.semiLocalIntegralSet K L v} = 1)
    (J' : ℂ)
    (hJ' : AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (diagUnits2 α β) τ'
      ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)) J') :
    J' = if ‖(a : v.adicCompletion K)‖ = 1 ∧ ‖(b : v.adicCompletion K)‖ = 1 then
        (Module.finrank K L : ℂ) *
          (((2 * Real.log (Ideal.absNorm v.asIdeal) *
              ∑ s ∈ Finset.range (m.toNat + 1),
                (s : ℝ) * ((Ideal.absNorm v.asIdeal : ℝ) ^ s -
                  (Ideal.absNorm v.asIdeal : ℝ) ^ s / (Ideal.absNorm v.asIdeal : ℝ)) : ℝ) : ℂ))
      else 0 := by sorry
