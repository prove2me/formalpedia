-- Prove2me | Theorems.Thm_ExploreFirst_Relative_pinsker_step
-- name    : ExploreFirst.Relative.pinsker_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:13:05.629789+00:00
-- url     : https://prove2.me/theorems/3369fa99-4088-41b9-89bf-4829f339ebd0
-- title:
--   Proof of Theorem 3, p. 12 — via Pinsker, r/(1 + r) ≥ 1/2 − √(T KL(ν_a, ν′_a)/(2K))
-- statement:
--   Under the hypotheses of the symmetry identity (a model $\mathcal{D}$, a strategy $\psi$ pairwise symmetric for optimal arms on $\mathcal{D}$, a bandit problem $\underline{\nu}$ in $\mathcal{D}$, a suboptimal arm $a$, an optimal arm $a^\star$, the alternative $\underline{\nu}'$ with $\nu'_k = \nu_k$ for $k \ne a$ and $\nu'_a = \nu_{a^\star}$, and $T \ge 1$), assume moreover that
--
--   1. $\mathrm{KL}(\nu_a, \nu'_a) < +\infty$;
--   2. $\mathbb{E}_{\underline{\nu}}[N_{\psi,a}(T)] \le T/K$;
--   3. $r \le 1$, where $r = \mathbb{E}_{\underline{\nu}}\big[N^+_{\psi,a}(T)/N^+_{\psi,a^\star}(T)\big]$ and $N^+_{\psi,k}(T) = \max\{N_{\psi,k}(T), 1\}$.
--
--   Then
--   $$\frac{r}{1+r} \;\ge\; \frac12 - \sqrt{\frac{T\,\mathrm{KL}(\nu_a, \nu'_a)}{2K}} .$$
--
--   Assumptions 2 and 3 are the two cases that the proof of Theorem 3 may assume, the other cases giving the theorem directly. The bound follows from (12), the Jensen step, the monotonicity of $p \mapsto \mathrm{kl}(p, 1/2)$ on $[0, 1/2]$ and Pinsker's inequality $\mathrm{kl}(p, 1/2) \ge 2(p - 1/2)^2$.
--
--   **Formalization Note** Assumption 1 is added so that $\mathrm{KL}(\nu_a,\nu'_a)$ can be used as a real number; when it is $+\infty$ the paper's bound reads $-\infty$ and says nothing.
-- source:
--   Garivier, Ménard, Stoltz, Explore First, Exploit Next, arXiv:1602.07182v3, p. 12, proof of Theorem 3, the display after "In particular,"

import Mathlib
import Definitions.Def_BanditPolicy
import Definitions.Def_ExploreFirst_Relative_Setting

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace ExploreFirst.Relative

theorem pinsker_step {K : ℕ} (𝒟 : Set (Measure ℝ)) (h𝒟 : ExploreFirst.Asymptotic.IsModel 𝒟)
    (π : BanditPolicy K) (hπ : IsPairwiseSymmetric 𝒟 π)
    (ν : StochasticBandit K) (hν : ExploreFirst.Asymptotic.InModel 𝒟 ν)
    (a a' : Fin K) (ha : 0 < banditGap ν a) (ha' : a' ∈ ExploreFirst.Asymptotic.optimalArms ν)
    (ν' : StochasticBandit K) (hν'_ne : ∀ k, k ≠ a → ν'.P k = ν.P k) (hν'_a : ν'.P a = ν.P a')
    (hKL : InformationTheory.klDiv (ν.P a) (ν'.P a) ≠ ⊤)
    (T : ℕ) (hT : 1 ≤ T)
    (hpulls : ExploreFirst.FundIneq.expPulls ν π T a ≤ (T : ℝ) / K)
    (hr : ∫ h, pullsPlus a h / pullsPlus a' h ∂(banditMeasure ν π T) ≤ 1) :
    1 / 2 - Real.sqrt ((T : ℝ) * (InformationTheory.klDiv (ν.P a) (ν'.P a)).toReal / (2 * K)) ≤
      (∫ h, pullsPlus a h / pullsPlus a' h ∂(banditMeasure ν π T)) /
        (1 + ∫ h, pullsPlus a h / pullsPlus a' h ∂(banditMeasure ν π T)) := by sorry

end ExploreFirst.Relative
