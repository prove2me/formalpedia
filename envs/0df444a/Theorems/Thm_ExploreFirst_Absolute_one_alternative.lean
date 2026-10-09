-- Prove2me | Theorems.Thm_ExploreFirst_Absolute_one_alternative
-- name    : ExploreFirst.Absolute.one_alternative
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:13:10.858168+00:00
-- url     : https://prove2.me/theorems/c4b0371c-c3bb-4e0d-82c7-8629ac81bfbf
-- title:
--   Theorem 2 proof — lower bound against one alternative arm law
-- statement:
--   Let $\mathcal D$ be a model of probability laws with finite means, and let $\psi$ be smarter than uniform on it. Suppose the bandit problem $\underline\nu$ belongs to $\mathcal D$. Replace arm $a$ by a law $\nu'_a\in\mathcal D$ whose mean exceeds the original optimal mean $\mu^*$, leaving all other arms unchanged. Assume $\mathrm{KL}(\nu_a,\nu'_a)<\infty$, $T\ge1$, and $\mathbb E_{\underline\nu}[N_{\psi,a}(T)]/T\le1/K$. Then
--   $$\frac{\mathbb E_{\underline\nu}[N_{\psi,a}(T)]}{T}\ge\frac1K-\sqrt{\frac{2T}{K^2}\mathrm{KL}(\nu_a,\nu'_a)}.$$
--
--   This one-alternative estimate is the last displayed inequality in the proof of Theorem 2. The upper bound on the original pull fraction is the case considered explicitly in that proof.
--
--   **Formalization Note** The alternative law belongs to the model, and the original problem does too, so Definition 2 applies to the modified problem. Finite divergence is stated before conversion to a real number.
-- source:
--   Garivier, Ménard, Stoltz, Explore First, Exploit Next, arXiv:1602.07182v3, p. 11, last display of the proof of Theorem 2

import Mathlib
import Definitions.Def_ExploreFirst_Absolute_Setting

namespace ExploreFirst.Absolute

/-- The one-alternative bound in the last display of Theorem 2's proof, p. 11. -/
theorem one_alternative {K : ℕ} (𝒟 : Set (MeasureTheory.Measure ℝ))
    (hmodel : ExploreFirst.Asymptotic.IsModel 𝒟) (π : BanditAlgorithm.BanditPolicy K)
    (hπ : IsSmarterThanUniform 𝒟 π)
    (ν ν' : BanditAlgorithm.StochasticBandit K) (hν : ExploreFirst.Asymptotic.InModel 𝒟 ν)
    (a : Fin K) (hother : ∀ k : Fin K, k ≠ a → ν'.P k = ν.P k)
    (ha : ν'.P a ∈ 𝒟)
    (hbest : BanditAlgorithm.banditOptimalMean ν < BanditAlgorithm.banditArmMean ν' a)
    (hkl : InformationTheory.klDiv (ν.P a) (ν'.P a) ≠ ⊤)
    (T : ℕ) (hT : 1 ≤ T)
    (hsmall : ExploreFirst.FundIneq.expPulls ν π T a / T ≤ 1 / (K : ℝ)) :
    1 / (K : ℝ) - Real.sqrt (2 * T / (K : ℝ) ^ 2 *
      (InformationTheory.klDiv (ν.P a) (ν'.P a)).toReal) ≤
      ExploreFirst.FundIneq.expPulls ν π T a / T := by sorry

end ExploreFirst.Absolute
