-- Prove2me | Theorems.Thm_ExploreFirst_Relative_symmetry_half
-- name    : ExploreFirst.Relative.symmetry_half
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:12:43.42396+00:00
-- url     : https://prove2.me/theorems/b61a8a79-3042-4cf4-b436-2478f6f4b5dd
-- title:
--   Proof of Theorem 3, p. 12, first display — 𝔼_ν̲′[N⁺_a/(N⁺_a + N⁺_{a⋆})] = 𝔼_ν̲′[N⁺_{a⋆}/(N⁺_{a⋆} + N⁺_a)] = 1/2
-- statement:
--   Let $\mathcal{D}$ be a model, $\psi$ a strategy that is pairwise symmetric for optimal arms on $\mathcal{D}$, and $\underline{\nu}$ a bandit problem in $\mathcal{D}$. Let $a$ be a suboptimal arm ($\Delta_a > 0$) and $a^\star$ an optimal arm of $\underline{\nu}$. Let $\underline{\nu}'$ be the alternative bandit problem with $\nu'_k = \nu_k$ for every $k \ne a$ and $\nu'_a = \nu_{a^\star}$. Write $N^+_{\psi,k}(T) = \max\{N_{\psi,k}(T), 1\}$. Then for every $T \ge 1$,
--   $$\mathbb{E}_{\underline{\nu}'}\left[\frac{N^+_{\psi,a}(T)}{N^+_{\psi,a}(T) + N^+_{\psi,a^\star}(T)}\right] = \mathbb{E}_{\underline{\nu}'}\left[\frac{N^+_{\psi,a^\star}(T)}{N^+_{\psi,a^\star}(T) + N^+_{\psi,a}(T)}\right] = \frac12 .$$
--
--   Under $\underline{\nu}'$ the arms $a$ and $a^\star$ are both optimal and have the same distribution, so pairwise symmetry applies to them. This identity is the value of $\mathbb{E}_{\underline{\nu}'}[Z]$ that enters the fundamental inequality (6) in the proof of Theorem 3.
--
--   **Formalization Note** Both equalities of the display are stated. The alternative problem $\underline{\nu}'$ is not constructed: the statement holds for every bandit problem $\underline{\nu}'$ that agrees with $\underline{\nu}$ off arm $a$ and has $\nu'_a = \nu_{a^\star}$. The standing assumption that $\mathcal{D}$ consists of probability measures with an expectation (§1.1, p. 3) is a hypothesis.
-- source:
--   Garivier, Ménard, Stoltz, Explore First, Exploit Next, arXiv:1602.07182v3, p. 12, proof of Theorem 3, first display

import Mathlib
import Definitions.Def_BanditPolicy
import Definitions.Def_ExploreFirst_Relative_Setting

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace ExploreFirst.Relative

theorem symmetry_half {K : ℕ} (𝒟 : Set (Measure ℝ)) (h𝒟 : ExploreFirst.Asymptotic.IsModel 𝒟)
    (π : BanditPolicy K) (hπ : IsPairwiseSymmetric 𝒟 π)
    (ν : StochasticBandit K) (hν : ExploreFirst.Asymptotic.InModel 𝒟 ν)
    (a a' : Fin K) (ha : 0 < banditGap ν a) (ha' : a' ∈ ExploreFirst.Asymptotic.optimalArms ν)
    (ν' : StochasticBandit K) (hν'_ne : ∀ k, k ≠ a → ν'.P k = ν.P k) (hν'_a : ν'.P a = ν.P a')
    (T : ℕ) (hT : 1 ≤ T) :
    (∫ h, pullsPlus a h / (pullsPlus a h + pullsPlus a' h) ∂(banditMeasure ν' π T) =
      ∫ h, pullsPlus a' h / (pullsPlus a' h + pullsPlus a h) ∂(banditMeasure ν' π T)) ∧
    (∫ h, pullsPlus a' h / (pullsPlus a' h + pullsPlus a h) ∂(banditMeasure ν' π T) = 1 / 2) := by sorry

end ExploreFirst.Relative
