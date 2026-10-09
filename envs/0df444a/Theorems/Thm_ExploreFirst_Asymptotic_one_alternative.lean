-- Prove2me | Theorems.Thm_ExploreFirst_Asymptotic_one_alternative
-- name    : ExploreFirst.Asymptotic.one_alternative
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:25:25.179532+00:00
-- url     : https://prove2.me/theorems/fd7f3f14-7dcf-4407-a0c2-2e61ce86daea
-- title:
--   Theorem 1 proof, p. 9 — asymptotic lower bound for one alternative
-- statement:
--   Let $\psi$ be uniformly fast convergent on a model $\mathcal D$. Let $\underline\nu$ belong to $\mathcal D$, and let $a$ be suboptimal. Form $\underline\nu'$ by replacing only arm $a$ with a law in $\mathcal D$ whose mean exceeds the original optimal mean. Then
--
--   $$
--   \liminf_{T\to\infty}
--   \frac{\mathbb E_{\underline\nu}N_{\psi,a}(T)}{\ln T}
--   \ge\frac1{\mathrm{KL}(\nu_a,\nu'_a)}.
--   $$
--
--   This is the bound obtained before optimizing over all admissible alternative laws, which produces the information cost $\mathcal K_{\inf}$ in Theorem 1.
--
--   **Formalization Note** The inequality is in the extended nonnegative reals: $1/0=+\infty$ and $1/+\infty=0$. The liminf uses the nonnegative ratio on natural horizons; the finitely many horizons at which $\ln T\le0$ do not change it.
-- source:
--   Garivier, Ménard, Stoltz, Explore First, Exploit Next, arXiv:1602.07182v3, p. 9, proof of Theorem 1, penultimate display

import Mathlib
import Definitions.Def_ExploreFirst_Asymptotic_Setting

namespace ExploreFirst.Asymptotic

theorem one_alternative {K : ℕ} (𝒟 : Set (MeasureTheory.Measure ℝ))
    (h𝒟 : IsModel 𝒟) (π : BanditAlgorithm.BanditPolicy K)
    (hπ : IsUniformlyFastConvergent 𝒟 π)
    (ν ν' : BanditAlgorithm.StochasticBandit K) (hν : InModel 𝒟 ν)
    (a : Fin K) (hsub : 0 < BanditAlgorithm.banditGap ν a)
    (hother : ∀ k, k ≠ a → ν'.P k = ν.P k)
    (ha : ν'.P a ∈ 𝒟)
    (hbest : BanditAlgorithm.banditOptimalMean ν < BanditAlgorithm.banditArmMean ν' a) :
    (InformationTheory.klDiv (ν.P a) (ν'.P a))⁻¹ ≤
      Filter.liminf (fun T : ℕ =>
        ENNReal.ofReal (ExploreFirst.FundIneq.expPulls ν π T a / Real.log T)) Filter.atTop := by sorry

end ExploreFirst.Asymptotic
