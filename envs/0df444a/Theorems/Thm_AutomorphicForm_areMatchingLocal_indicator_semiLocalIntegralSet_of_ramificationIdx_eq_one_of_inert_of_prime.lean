-- Prove2me | Theorems.Thm_AutomorphicForm_areMatchingLocal_indicator_semiLocalIntegralSet_of_ramificationIdx_eq_one_of_inert_of_prime
-- name    : AutomorphicForm.areMatchingLocal_indicator_semiLocalIntegralSet_of_ramificationIdx_eq_one_of_inert_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/89c23133-82a3-5229-8d3b-670f1c5b3f77
-- title:
--   Inert unit fundamental lemma for twisted GL₂
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an extension of $K$ whose degree $\operatorname{finrank}_K L$ is prime, let $\sigma$ be an automorphism of $L$ over $K$ with $\sigma \neq 1$, and let $v$ be a nonzero prime of $\mathcal{O}_K$. Assume that every prime $w$ of $\mathcal{O}_L$ whose contraction to $\mathcal{O}_K$ is $v$ has ramification index $1$ over $v$, and that any two primes $w, w'$ of $\mathcal{O}_L$ contracting to $v$ are equal. The conclusion is the predicate `AreMatchingLocal` for $K$, $L$, $v$, $\sigma$ applied to the $\mathbb{C}$-valued indicator function of `semiLocalIntegralSet K L v` — the set of $g \in \mathrm{GL}_2(L \otimes_K K_v)$ such that both $g$ and $g^{-1}$ have all entries in the image of the integers of $L$ under the map to $L \otimes_K K_v$ — and the indicator function of `localIntegralSet K v`, the set of $g \in \mathrm{GL}_2(K_v)$ with $g$ and $g^{-1}$ having entries in $\mathcal{O}_v$. Unfolded, this asserts, for the Haar measures `semiLocalHaar K L v` and `localHaar K v`, first that for every $\delta$ with $\operatorname{norm\,string}$ regular semisimple, every regular semisimple $\gamma \in \mathrm{GL}_2(K_v)$, every norm conjugator $y$ and every coupled pair of Haar measures on the centraliser of $\gamma$ and on the $\sigma$-twisted centraliser of $\delta$, any value of the twisted orbital integral of the first indicator equals any value of the orbital integral of the second; and second that for every regular semisimple $\gamma$ which is the norm of no $\delta$, every value of the orbital integral of the second indicator against any Haar measure on the centraliser of $\gamma$ is $0$.
--
--   This is the unit case of the fundamental lemma for base change of $\mathrm{GL}_2$ at a place $v$ of $K$ that is unramified and inert in $L$, the hypotheses saying that exactly one place of $L$ lies above $v$ and that it is unramified, so that $L \otimes_K K_v$ is the unramified extension of $K_v$ of degree $[L:K]$. It is obtained from the corresponding statement for a chosen extension $w$ of $v$ together with a uniformiser and an isomorphism $L \otimes_K K_v \cong L_w$, and feeds into the place-by-place matching statement [`AutomorphicForm.areMatchingLocal_indicator_semiLocalIntegralSet_of_ramificationIdx_eq_one_of_prime`](thm.html#AutomorphicForm.areMatchingLocal_indicator_semiLocalIntegralSet_of_ramificationIdx_eq_one_of_prime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_areMatchingLocal_indicator_semiLocalIntegralSet_of_ramificationIdx_eq_one_of_inert_of_prime.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem AutomorphicForm.areMatchingLocal_indicator_semiLocalIntegralSet_of_ramificationIdx_eq_one_of_inert_of_prime
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime)
    (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (hinert : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = v → HeightOneSpectrum.under (𝓞 K) w' = v → w = w') :
    AreMatchingLocal K L v σ ((semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))
      ((localIntegralSet K v).indicator fun _ => (1 : ℂ)) := by sorry
