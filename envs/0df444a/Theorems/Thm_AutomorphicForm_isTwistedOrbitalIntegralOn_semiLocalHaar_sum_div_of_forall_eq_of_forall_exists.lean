-- Prove2me | Theorems.Thm_AutomorphicForm_isTwistedOrbitalIntegralOn_semiLocalHaar_sum_div_of_forall_eq_of_forall_exists
-- name    : AutomorphicForm.isTwistedOrbitalIntegralOn_semiLocalHaar_sum_div_of_forall_eq_of_forall_exists
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/82a53300-9ba1-5b77-a8c8-bf2d031b56c7
-- title:
--   Twisted orbital integral as a finite double-coset sum
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $v$ be a nonzero prime of $\mathcal{O}_K$, let $\sigma$ be a $K$-algebra automorphism of $L$, write $A = L \otimes_K K_v$, and let $\delta \in \mathrm{GL}_2(A)$. Let $\sigma$ act on $\mathrm{GL}_2(A)$ through $\sigma \otimes \mathrm{id}$ ([`AutomorphicForm.sigmaGL`](def/AutomorphicForm_TwistedOrbital.html#L202)), and assume the norm string $\delta\,\sigma(\delta)\cdots\sigma^{[L:K]-1}(\delta)$ is regular semisimple, i.e. its $\mathrm{tr}^2 - 4\det$ is a unit of $A$. Let $T = \{t : t\delta\sigma(t)^{-1} = \delta\}$ be the $\sigma$-twisted centraliser of $\delta$, carrying a Haar measure $\tau'$ for its Borel structure, and let $U$ be the set of $g \in \mathrm{GL}_2(A)$ such that both $g$ and $g^{-1}$ have entries in the image of $\mathcal{O}_L \otimes \mathcal{O}_{K_v}$ in $A$. Let $\varphi : \mathrm{GL}_2(A) \to \mathbb{C}$ satisfy $\varphi(u_1 g u_2) = \varphi(g)$ for all $g$ and all $u_1, u_2 \in U$, and let $S$ be a finite subset of $\mathrm{GL}_2(A)$ such that (i) whenever $s, s' \in S$ and $s' = t s u$ with $t \in T$, $u \in U$, then $s' = s$, and (ii) every $x$ with $\varphi(x^{-1}\delta\sigma(x)) \neq 0$ lies in $T s U$ for some $s \in S$. Then the number $$\sum_{s \in S} \frac{\varphi(s^{-1}\delta\sigma(s))}{\tau'\{t \in T : s^{-1} t s \in U\}}$$ is a value of the twisted orbital integral of $\varphi$ at $\delta$ with respect to the Haar measure on $\mathrm{GL}_2(A)$ normalised by $U$ and the measure $\tau'$ on $T$: there is a nonnegative, measurable, compactly supported $w : \mathrm{GL}_2(A) \to \mathbb{R}$ with $\int_T w(tx)\,d\tau' = 1$ for every $x$ with $\varphi(x^{-1}\delta\sigma(x)) \neq 0$, for which the displayed sum equals $\int \varphi(x^{-1}\delta\sigma(x))\,w(x)\,d\mu$.
--
--   This is the elementary evaluation of a semi-local twisted orbital integral of a $U$-bi-invariant function as a finite sum over the twisted double cosets $T \backslash \mathrm{GL}_2(A) / U$ that meet the support, each term weighted by the inverse volume of $T \cap sUs^{-1}$. It is used in the comparison of twisted orbital integrals with ordinary ones at inert primes, namely by [`AutomorphicForm.exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime`](thm.html#AutomorphicForm.exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime) and [`AutomorphicForm.twistedOrbitalIntegral_eq_shadow_of_irreducible_charpoly`](thm.html#AutomorphicForm.twistedOrbitalIntegral_eq_shadow_of_irreducible_charpoly).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isTwistedOrbitalIntegralOn_semiLocalHaar_sum_div_of_forall_eq_of_forall_exists.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory TensorProduct
open scoped TensorProduct.RightActions

theorem
AutomorphicForm.isTwistedOrbitalIntegralOn_semiLocalHaar_sum_div_of_forall_eq_of_forall_exists
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsRegularSemisimple
      (AutomorphicForm.normString K L (v.adicCompletion K) σ δ))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    (φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hφ : ∀ g : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      ∀ u₁ ∈ AutomorphicForm.semiLocalIntegralSet K L v, ∀ u₂ ∈ AutomorphicForm.semiLocalIntegralSet K L v,
        φ (u₁ * g * u₂) = φ g)
    (S : Finset (GL (Fin 2) (L ⊗[K] v.adicCompletion K)))
    (hS :
      ∀ s ∈ S, ∀ s' ∈ S,
        ∀ t ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ,
          ∀ u ∈ AutomorphicForm.semiLocalIntegralSet K L v, s' = t * s * u → s' = s)
    (hcov :
      ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        φ (x⁻¹ * δ * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x) ≠ 0 →
          ∃ s ∈ S,
            ∃ t ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ,
              ∃ u ∈ AutomorphicForm.semiLocalIntegralSet K L v, x = t * s * u) :
    AutomorphicForm.IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ
      (AutomorphicForm.semiLocalHaar K L v) δ τ' φ
      (∑ s ∈ S, φ (s⁻¹ * δ * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ s) /
        ((τ' {t | s⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * s ∈
            AutomorphicForm.semiLocalIntegralSet K L v}).toReal : ℂ)) := by sorry
