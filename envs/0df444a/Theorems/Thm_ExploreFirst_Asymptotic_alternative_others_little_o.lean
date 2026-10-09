-- Prove2me | Theorems.Thm_ExploreFirst_Asymptotic_alternative_others_little_o
-- name    : ExploreFirst.Asymptotic.alternative_others_little_o
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:29:31.638072+00:00
-- url     : https://prove2.me/theorems/c5e1541d-fbdc-4d77-ba4a-8576275a7b55
-- title:
--   Theorem 1 proof, p. 9 — eventual bound on draws of the alternative's other arms
-- statement:
--   Let $\psi$ be uniformly fast convergent on a model $\mathcal D$, and let $\underline\nu$ belong to that model. Replace arm $a$ by a law in $\mathcal D$ whose mean exceeds the original optimal mean, leaving every other arm law unchanged; call the new bandit $\underline\nu'$. For every $0<\alpha\le1$, all sufficiently large $T$ satisfy
--
--   $$
--   T-\mathbb E_{\underline\nu'}N_{\psi,a}(T)\le T^\alpha.
--   $$
--
--   Every arm other than $a$ is suboptimal in the alternative problem, so this is the eventual estimate extracted from the proof's $o(T^\alpha)$ display.
--
--   **Formalization Note** The model requires probability laws with integrable rewards. Horizons are natural numbers, and the estimate is an eventual real inequality.
-- source:
--   Garivier, Ménard, Stoltz, Explore First, Exploit Next, arXiv:1602.07182v3, p. 9, proof of Theorem 1, display immediately following (11) and its ‘in particular’ sentence

import Mathlib
import Definitions.Def_ExploreFirst_Asymptotic_Setting

namespace ExploreFirst.Asymptotic

theorem alternative_others_little_o {K : ℕ} (𝒟 : Set (MeasureTheory.Measure ℝ))
    (h𝒟 : IsModel 𝒟) (π : BanditAlgorithm.BanditPolicy K)
    (hπ : IsUniformlyFastConvergent 𝒟 π)
    (ν ν' : BanditAlgorithm.StochasticBandit K) (hν : InModel 𝒟 ν)
    (a : Fin K) (hother : ∀ k, k ≠ a → ν'.P k = ν.P k)
    (ha : ν'.P a ∈ 𝒟)
    (hbest : BanditAlgorithm.banditOptimalMean ν < BanditAlgorithm.banditArmMean ν' a)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ᶠ T : ℕ in Filter.atTop,
      (T : ℝ) - ExploreFirst.FundIneq.expPulls ν' π T a ≤ (T : ℝ) ^ α := by sorry

end ExploreFirst.Asymptotic
