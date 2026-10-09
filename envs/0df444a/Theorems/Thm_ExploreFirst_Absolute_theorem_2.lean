-- Prove2me | Theorems.Thm_ExploreFirst_Absolute_theorem_2
-- name    : ExploreFirst.Absolute.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:12:30.309812+00:00
-- url     : https://prove2.me/theorems/a07b7a06-55eb-440d-ac24-2e5bd7b9b7a8
-- title:
--   Theorem 2 — absolute lower bound for every arm
-- statement:
--   Let $\mathcal D$ be a model of probability laws with finite means, let $\psi$ be a strategy smarter than uniform on $\mathcal D$, and let the $K$-armed bandit problem $\underline\nu$ belong to $\mathcal D$. For every arm $a$ and integer $T\ge1$, if $\mathcal K_{\inf}(\nu_a,\mu^*,\mathcal D)<\infty$, then
--   $$\mathbb E_{\underline\nu}[N_{\psi,a}(T)]\ge\frac{T}{K}\left(1-\sqrt{2T\mathcal K_{\inf}(\nu_a,\mu^*,\mathcal D)}\right).$$
--
--   Here $\mu^*$ is the largest arm mean, and $\mathcal K_{\inf}$ is the infimum of $\mathrm{KL}(\nu_a,Q)$ over model laws $Q$ with mean greater than $\mu^*$. The bound applies to optimal and suboptimal arms alike. It quantifies the initial exploration forced by Definition 2.
--
--   **Formalization Note** The paper prints “all bandit problems,” but its proof requires $\underline\nu\in\mathcal D$ when applying Definition 2 to a one-arm alternative. When $\mathcal K_{\inf}=+\infty$, the printed right-hand side is $-\infty$; the real-valued Lean statement therefore takes the finite case. The case $\mathcal K_{\inf}=0$ is included.
-- source:
--   Garivier, Ménard, Stoltz, Explore First, Exploit Next, arXiv:1602.07182v3, p. 10, Theorem 2, first display; proof p. 11

import Mathlib
import Definitions.Def_ExploreFirst_Absolute_Setting

namespace ExploreFirst.Absolute

/-- Garivier–Ménard–Stoltz, Theorem 2, p. 10, with the necessary model-membership and finite-divergence conditions. -/
theorem theorem_2 {K : ℕ} (𝒟 : Set (MeasureTheory.Measure ℝ))
    (hmodel : ExploreFirst.Asymptotic.IsModel 𝒟) (π : BanditAlgorithm.BanditPolicy K)
    (hπ : IsSmarterThanUniform 𝒟 π)
    (ν : BanditAlgorithm.StochasticBandit K) (hν : ExploreFirst.Asymptotic.InModel 𝒟 ν)
    (a : Fin K)
    (hfinite : BanditAlgorithm.banditDInf 𝒟 (ν.P a) (BanditAlgorithm.banditOptimalMean ν) ≠ ⊤)
    (T : ℕ) (hT : 1 ≤ T) :
    (T : ℝ) / K * (1 - Real.sqrt (2 * T *
      (BanditAlgorithm.banditDInf 𝒟 (ν.P a) (BanditAlgorithm.banditOptimalMean ν)).toReal)) ≤
      ExploreFirst.FundIneq.expPulls ν π T a := by sorry

end ExploreFirst.Absolute
