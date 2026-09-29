-- Prove2me | Theorems.Thm_AutomorphicForm_eq_ite_finrank_mul_sum_of_isTwistedWeightedOrbitalIntegral_indicator_semiLocalIntegralSet_of_nontrivial_extension
-- name    : AutomorphicForm.eq_ite_finrank_mul_sum_of_isTwistedWeightedOrbitalIntegral_indicator_semiLocalIntegralSet_of_nontrivial_extension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/b652859d-a2a9-5cd4-8a99-1eef39b9e6d0
-- title:
--   Twisted weighted orbital integral of the unit at a split place
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra whose degree $\ell=[L:K]$ is prime, let $\sigma$ be a $K$-automorphism of $L$ with $\sigma\neq1$, and let $v$ be a nonzero prime of $\mathcal O_K$ such that every prime $w$ of $\mathcal O_L$ lying under $v$ has ramification index $1$ over $v$ and such that the type of primes of $\mathcal O_L$ lying over $v$ is nontrivial, i.e. at least two primes lie above $v$. Let $a\neq b$ be units of the completion $K_v$ and $m\in\mathbb Z$ with $\|a-b\|=q^{-m}$, where $q$ is the absolute norm of $v$. Let $\alpha,\beta$ be units of $L\otimes_K K_v$ such that the norm string of $\delta=\mathrm{diag}(\alpha,\beta)$, namely the product $\delta\,\sigma(\delta)\cdots\sigma^{\ell-1}(\delta)$ taken along $\sigma$ acting on $L\otimes_K K_v$ and entrywise on $\mathrm{GL}_2$, equals the image of $\mathrm{diag}(a,b)$ under the map $\mathrm{GL}_2(K_v)\to\mathrm{GL}_2(L\otimes_K K_v)$ induced by $x\mapsto 1\otimes x$. Let $\tau'$ be a Haar measure, for the Borel structure, on the $\sigma$-twisted centraliser $\{t\mid t\,\delta\,\sigma(t)^{-1}=\delta\}$ of $\delta$ in $\mathrm{GL}_2(L\otimes_K K_v)$, normalised so that the set of its elements whose underlying matrix lies in [`AutomorphicForm.semiLocalIntegralSet K L v`](def/AutomorphicForm_TwistedOrbital.html#L136) — those $g$ for which $g$ and $g^{-1}$ have all entries in the image of $\mathcal O_L\otimes\mathcal O_{K_v}$ in $L\otimes_K K_v$ — has measure $1$. Finally let $J'\in\mathbb C$ be a twisted weighted orbital integral of the characteristic function of that integral set at $\delta$: there is a real-valued function $s$ on $\mathrm{GL}_2(L\otimes_K K_v)$ satisfying the twisted section predicate [`AutomorphicForm.IsTwistedSectionFnOn`](def/AutomorphicForm_TwistedOrbital.html#L278) for these data such that $J'=\int \mathbf 1(x^{-1}\delta\,\sigma(x))\cdot\mathrm{wt}(x)\cdot s(x)$ against the Haar measure [`AutomorphicForm.semiLocalHaar K L v`](def/AutomorphicForm_TwistedOrbital.html#L169), the weight $\mathrm{wt}$ being the sum over the primes $w$ above $v$ of the local weights of the components of $x$. Then $J'=0$ unless $\|a\|=\|b\|=1$, in which case $$J'=\ell\cdot\Bigl(2\log q\sum_{s=0}^{\max(m,0)} s\,\bigl(q^{s}-q^{s}/q\bigr)\Bigr),$$ the real value being viewed in $\mathbb C$.
--
--   This is the twisted side, at a place of $K$ that is unramified and not inert in the prime-degree extension $L/K$, of the weighted fundamental lemma for the unit of the local Hecke algebra: the twisted weighted orbital integral of the characteristic function of the integral points is $\ell$ times the corresponding untwisted integral at $\mathrm{diag}(a,b)$. It is used by [`AutomorphicForm.twistedWeighted_eq_finrank_mul_weighted_indicator_of_unramified`](thm.html#AutomorphicForm.twistedWeighted_eq_finrank_mul_weighted_indicator_of_unramified), which records that comparison.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_eq_ite_finrank_mul_sum_of_isTwistedWeightedOrbitalIntegral_indicator_semiLocalIntegralSet_of_nontrivial_extension.lean

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.eq_ite_finrank_mul_sum_of_isTwistedWeightedOrbitalIntegral_indicator_semiLocalIntegralSet_of_nontrivial_extension
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (hsplit : Nontrivial (v.Extension (𝓞 L)))
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
