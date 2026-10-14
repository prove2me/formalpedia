-- Prove2me | Theorems.Thm_FirstPriceLearning_Adversarial_theorem_2
-- name    : FirstPriceLearning.Adversarial.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:34:07.063925+00:00
-- url     : https://prove2.me/theorems/5e2d4d2f-b7fe-4b57-aeca-a78fbbdbe3ed
-- title:
--   Theorem 2 — bidding with arbitrary private values: $\mathbb E[R_T(\pi;v)]\le C\sqrt T\log^3T$
-- statement:
--   There is an absolute constant $C>0$ with the following property. For every horizon $T\ge2$ there is a bidding policy $\pi$ that uses only censored feedback such that, for every value sequence $v_1,\dots,v_T\in[0,1]$ chosen by an oblivious adversary and every CDF $G$ of the highest other bids on $[0,1]$,
--   $$
--   \mathbb E\big[R_T(\pi;v)\big]\le C\sqrt T\log^3T,
--   $$
--   where the expectation is over the randomness of the policy and of the iid HOBs. The ML-IS-UCB policy of Section 4.2 is such a policy.
--
--   Together with the $\Omega(\sqrt T)$ lower bound, this shows that $\widetilde\Theta(\sqrt T)$ regret is achievable in repeated first-price auctions with censored feedback even when the values are adversarial, for an arbitrary unknown $G$.
--
--   **Formalization Note** The constant $C$ is chosen before $T$, the policy may depend on $T$ but not on $v$ or $G$, and the policy is quantified over the class of non-anticipating randomized policies with censored feedback defined in the model. An oblivious adversary is a fixed deterministic sequence, which is universally quantified. $T\ge2$ is added (slip 1): for $T=1$ the right-hand side is $0$ while some value and HOB law force positive regret on any first bid. The conclusion also asserts integrability of the regret. $\log$ is the natural logarithm.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 10, Theorem 2

import Mathlib
import Definitions.Def_FirstPriceLearning_Adversarial_Model
import Definitions.Def_FirstPriceLearning_Adversarial_MLISUCB

open MeasureTheory

namespace FirstPriceLearning.Adversarial

/-- Theorem 2, p. 10: there is an absolute constant `C > 0` such that for every horizon `T ≥ 2`
there is a non-anticipating bidding policy `π` with censored feedback (ML-IS-UCB) whose expected
regret against every oblivious value sequence `v ∈ [0,1]^T` and every HOB law `G` on `[0, 1]` is
at most `C √T log³ T`; the expectation is over the policy's internal randomness and the iid HOBs. -/
theorem theorem_2 :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℕ, 2 ≤ T → ∃ π : Policy T,
      ∀ v : Fin T → ℝ, (∀ t, v t ∈ Set.Icc (0 : ℝ) 1) →
      ∀ (μG : Measure ℝ) [IsProbabilityMeasure μG], μG (Set.Icc (0 : ℝ) 1)ᶜ = 0 →
        Integrable (fun p : π.U × (Fin T → ℝ) => regret μG v (runBids (π.bid p.1) v p.2))
            (π.μU.prod (Measure.pi fun _ : Fin T => μG)) ∧
          expectedRegret π μG v ≤ C * Real.sqrt T * Real.log T ^ 3 := by sorry

end FirstPriceLearning.Adversarial
