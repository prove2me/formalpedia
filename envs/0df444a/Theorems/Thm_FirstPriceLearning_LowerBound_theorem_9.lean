-- Prove2me | Theorems.Thm_FirstPriceLearning_LowerBound_theorem_9
-- name    : FirstPriceLearning.LowerBound.theorem_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T10:14:26.724999+00:00
-- url     : https://prove2.me/theorems/fb12c408-3a8a-4080-9a7d-3b77488a2188
-- title:
--   Theorem 9 — even with full information and $v_t\equiv1$, every bidding policy has worst-case expected regret $\ge c\sqrt T$
-- statement:
--   Consider $T$ repeated first-price auctions in which the bidder's value is $v_t=1$ in every round and the highest other bid $m_t$ is revealed at the end of each round (full information). The HOBs $m_1,\dots,m_T$ are iid from a CDF $G$ on $[0,1]$, the expected reward of bid $b$ is $R(1,b)=(1-b)G(b)$, and the regret of a policy $\pi$ is $R_T(\pi;v)=\sum_{t=1}^T\bigl(\max_{b\in[0,1]}R(1,b)-R(1,b_t)\bigr)$.
--
--   There is an absolute constant $c>0$, independent of $T$, such that
--
--   $$
--   \inf_\pi\sup_G\ \mathbb E_G\bigl[R_T(\pi;v)\bigr]\ \ge\ c\sqrt T ,
--   $$
--
--   where the supremum is over all CDFs $G$ of the HOB on $[0,1]$ and the infimum over all policies, randomized ones included.
--
--   This shows that the $\widetilde O(\sqrt T)$ regret of the paper's policies under censored feedback is optimal up to logarithmic factors: even full information about the competing bids and a constant value cannot beat $\sqrt T$.
--
--   **Formalization Note** The statement is the stronger form "there is $c>0$ such that for every $T\ge1$ and every policy $\pi$ there is a HOB law $G$, a probability measure on $\mathbb R$ giving no mass outside $[0,1]$, with $\mathbb E_G[R_T(\pi;v)]\ge c\sqrt T$", which implies the inf–sup bound; the constant is chosen before $T$ and the policy, and the law after the policy. Policies are randomized: they draw internal randomness from an arbitrary probability space and bid in $[0,1]$ as a jointly measurable function of that randomness and the HOBs of the earlier rounds. The paper's proof gives $c=1/(24e^2)$.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 36, App. B, Theorem 9

import Mathlib
import Definitions.Def_FirstPriceLearning_LowerBound_Model

open MeasureTheory

namespace FirstPriceLearning.LowerBound

/-- arXiv:2003.09795v7, App. B, Theorem 9, p. 36: even with `v_t ≡ 1` and the HOBs revealed at the end
of each round, there is an absolute constant `c > 0` such that for every horizon `T ≥ 1` and every
randomized full-information policy `π` some HOB law `G` on `[0, 1]` forces `E_G[R_T(π; v)] ≥ c√T`
(the form `∀ π, ∃ G`, which implies `inf_π sup_G E_G[R_T(π; v)] ≥ c√T`). -/
theorem theorem_9 :
    ∃ c : ℝ, 0 < c ∧
      ∀ T : ℕ, 1 ≤ T → ∀ (U : Type) [MeasurableSpace U] (π : FullInfoPolicy T U),
        ∃ μG : Measure ℝ, IsProbabilityMeasure μG ∧ μG (Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧
          c * Real.sqrt T ≤ expectedRegret π μG := by sorry

end FirstPriceLearning.LowerBound
