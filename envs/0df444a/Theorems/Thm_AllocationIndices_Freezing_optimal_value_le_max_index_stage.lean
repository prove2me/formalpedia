-- Prove2me | Theorems.Thm_AllocationIndices_Freezing_optimal_value_le_max_index_stage
-- name    : AllocationIndices.Freezing.optimal_value_le_max_index_stage
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-01T15:07:07.094859+00:00
-- url     : https://prove2.me/theorems/440a03b1-ecd7-48f9-bbb6-a4574e8497af
-- title:
--   Stage inequality: over a stage of one bandit, $R(\mathcal F)$ earns at most at rate $\max_j \nu(B_j)$
-- statement:
--   Let $\mathcal F$ be a simple family of $k$ alternative bandit processes $B_1,\dots,B_k$ sharing a countable state space $T$, a transition kernel $P$, a bounded reward $r$ and a discount factor $0<a<1$, and let $x=(x_1,\dots,x_k)$ be the current state-vector. Write
--   $$R(\mathcal F,x)=\sup_g R_g(\mathcal F,x)$$
--   for the supremum, over all policies $g$, of the expected total discounted reward, and $\nu(B_j,x_j)$ for the index (2.6) of $B_j$ in state $x_j$.
--
--   Fix a bandit $B_i$ and a positive stopping time $\tau$ (values in $\{1,2,\dots\}\cup\{\infty\}$) of the evolution $x_i(0)=x_i, x_i(1), x_i(2),\dots$ of $B_i$ alone, and let $W_\tau(B_i,x_i)=E\sum_{t<\tau}a^t$. Let $x^{(\tau)}$ be the state-vector obtained from $x$ by replacing the state of $B_i$ by $x_i(\tau)$ (the state reached when $B_i$ has been continued for $\tau$ periods), and put $a^\infty=0$. Then
--   $$R(\mathcal F,x)\;\le\;\Big(\max_{1\le j\le k}\nu(B_j,x_j)\Big)\,W_\tau(B_i,x_i)\;+\;E\big[a^{\tau}\,R(\mathcal F,x^{(\tau)})\big].$$
--
--   In words: over a stage in which a single bandit is continued up to a stopping time, no policy can do better than earning at the constant rate $\max_j\nu(B_j)=\nu(\mathcal F)$ (Lemma 4.6(i)) for the discounted duration of the stage and then behaving optimally from the state-vector reached. This is the stage comparison of the freezing-and-promotion proof of the index theorem (§4.5), and it is the inequality that Corollary 4.16 applies at the start of each stage of an $\varepsilon$-index* policy: if $\nu_\tau(B_i)\ge\max_j\nu(B_j)-\varepsilon$, the stage loses at most $\varepsilon W_\tau(B_i)$ relative to the optimum.
--
--   **Formalization Note** $R(\mathcal F,\cdot)$ is the real supremum of the published `markovBanditDiscountedValue` over all `MarkovBanditPolicy`s, which is finite because $r$ is bounded. The state $x_i(\tau)$ is read off the trajectory as `ω (τ ω).toNat`; on $\{\tau=\infty\}$ the factor `discountPow a ⊤ = 0` kills the term. The expectation is over the law `markovChainMeasure P (x i)` of $B_i$ started at $x_i$.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033: §4.5 pp. 91–93 (proof of Theorem 2.1 by freezing and promotion rules, using Lemma 4.6(i) ν(F) = max_j ν(B_j)), stage inequality as applied to the stages of ε-index* policies in Corollary 4.16, §4.10 pp. 111–112

import Definitions.Def_AllocationIndices_Freezing_Model

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace AllocationIndices.Freezing

theorem optimal_value_le_max_index_stage {T : Type*} [MeasurableSpace T] [Countable T]
    [MeasurableSingletonClass T] (P : Kernel T T) [IsMarkovKernel P] {r : T → ℝ}
    (hr : BoundedReward r) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {k : ℕ} (x : Fin k → T)
    (i : Fin k) {τ : (ℕ → T) → ℕ∞} (hτ : IsPositiveStoppingTime τ) :
    (⨆ π : MarkovBanditPolicy k T, markovBanditDiscountedValue P r a π x) ≤
      (⨆ j : Fin k, gittinsIndex P r a (x j)) * stoppedTime P a τ (x i) +
        ∫ ω, discountPow a (τ ω) *
            (⨆ π : MarkovBanditPolicy k T, markovBanditDiscountedValue P r a π
              (Function.update x i (ω (τ ω).toNat))) ∂markovChainMeasure P (x i) := by sorry

end AllocationIndices.Freezing
