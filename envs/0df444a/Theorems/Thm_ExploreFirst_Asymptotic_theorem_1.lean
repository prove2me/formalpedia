-- Prove2me | Theorems.Thm_ExploreFirst_Asymptotic_theorem_1
-- name    : ExploreFirst.Asymptotic.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:26:33.432976+00:00
-- url     : https://prove2.me/theorems/1de37dee-3ff0-47f4-94c4-7160eec67cc8
-- title:
--   Theorem 1, p. 9 — asymptotic per-arm draw lower bound
-- statement:
--   Let $\mathcal D$ be a model of reward laws with finite expectations, and let $\psi$ be uniformly fast convergent on $\mathcal D$. Consider a bandit problem $\underline\nu$ whose arm laws all belong to $\mathcal D$. For each arm $a$ with mean strictly below the optimal mean $\mu^\star$, define
--
--   $$
--   \mathcal K_{\inf}(\nu_a,\mu^\star,\mathcal D)
--     =\inf\{\mathrm{KL}(\nu_a,Q):Q\in\mathcal D,\ \mathbb E_Q[X]>\mu^\star\},
--   $$
--
--   with the infimum of the empty set equal to $+\infty$. The expected number of draws of $a$ obeys
--
--   $$
--   \liminf_{T\to\infty}
--   \frac{\mathbb E_{\underline\nu}N_{\psi,a}(T)}{\ln T}
--   \ge\frac1{\mathcal K_{\inf}(\nu_a,\mu^\star,\mathcal D)}.
--   $$
--
--   The result identifies the asymptotic information cost of avoiding a suboptimal arm for every strategy in the stated class.
--
--   **Formalization Note** The paper's theorem sentence omits $\underline\nu\in\mathcal D$, but its proof applies uniform fast convergence to $\underline\nu$; that necessary condition is included. Arms are zero-based, policies are history-dependent Markov kernels, and the liminf is in extended nonnegative reals, preserving the cases $\mathcal K_{\inf}=0$ and $+\infty$.
-- source:
--   Garivier, Ménard, Stoltz, Explore First, Exploit Next, arXiv:1602.07182v3, p. 9, Theorem 1; p. 4, definition of 𝒦_inf

import Mathlib
import Definitions.Def_ExploreFirst_Asymptotic_Setting

namespace ExploreFirst.Asymptotic

theorem theorem_1 {K : ℕ} (𝒟 : Set (MeasureTheory.Measure ℝ))
    (h𝒟 : IsModel 𝒟) (π : BanditAlgorithm.BanditPolicy K)
    (hπ : IsUniformlyFastConvergent 𝒟 π)
    (ν : BanditAlgorithm.StochasticBandit K) (hν : InModel 𝒟 ν)
    (a : Fin K) (hsub : 0 < BanditAlgorithm.banditGap ν a) :
    (BanditAlgorithm.banditDInf 𝒟 (ν.P a) (BanditAlgorithm.banditOptimalMean ν))⁻¹ ≤
      Filter.liminf (fun T : ℕ =>
        ENNReal.ofReal (ExploreFirst.FundIneq.expPulls ν π T a / Real.log T)) Filter.atTop := by sorry

end ExploreFirst.Asymptotic
