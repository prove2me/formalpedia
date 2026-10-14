-- Prove2me | Theorems.Thm_FirstPriceLearning_GraphFeedback_lemma_1
-- name    : FirstPriceLearning.GraphFeedback.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:28:30.595529+00:00
-- url     : https://prove2.me/theorems/0d142c0e-661a-44b5-86a9-0cccbeff9eb9
-- title:
--   Lemma 1 — concentration of the empirical rewards of Algorithm 1 under graph feedback
-- statement:
--   Consider a stochastic multi-armed bandit with graph feedback (Definition 1): actions $\mathcal A = [K]$, a feedback graph $G = (\mathcal A, E)$ without self-loops, and iid reward vectors $r_1, \dots, r_T$ from a law $P$ on $[0,1]^K$ with mean rewards $R_a$. Run Algorithm 1 with either option, any admissible tie-breaking rule and failure probability $\delta \in (0,1)$. Write $n^t_a$ for the number of rounds $s \le t$ in which the reward of $a$ was revealed and $\bar r^t_a$ for the mean of those revealed rewards. Assume $KT \ge 2$.
--
--   Then, with probability at least $1-\delta$ over the rewards,
--   $$
--   \big|\bar r^t_a - R_a\big| \le 3\sqrt{\frac{\log(2T)\log(KT/\delta)}{n^t_a}}
--   $$
--   for every $t \in [T]$ and every $a \in \mathcal A$ with $n^t_a \ge 1$.
--
--   This is the concentration step behind Theorem 3: the revealed rewards of an action form a martingale sequence whose length is itself random, and the bound holds uniformly over all rounds and actions.
--
--   **Formalization Note** The printed lemma quantifies over all $(t, a)$; for $n^t_a = 0$ the right-hand side would be a division by zero, and the proof (p. 38) treats that case as vacuous, so the statement quantifies over $n^t_a \ge 1$. The case $K = T = 1$ is excluded: there the bound reads $|r_{1,1} - R_1| \le 3\sqrt{\log 2 \cdot \log(1/\delta)}$, which fails with probability $1 > \delta$ for a Bernoulli$(1/2)$ reward and $\delta = 0.99$. For $KT \ge 2$ the statement is unaffected. "With probability at least $1-\delta$" is the outer measure of the failure event under the product law $P^{\otimes T}$, at most $\delta$.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 13, Lemma 1 (proof: p. 38, App. C.1)

import Mathlib
import Definitions.Def_FirstPriceLearning_GraphFeedback_FeedbackGraph
import Definitions.Def_FirstPriceLearning_GraphFeedback_BanditModel
import Definitions.Def_FirstPriceLearning_GraphFeedback_ArmElimination

open MeasureTheory

namespace FirstPriceLearning.GraphFeedback

/-- Lemma 1 (p. 13), for Algorithm 1 with either option and any admissible tie-breaking rule:
with probability at least `1 − δ` over the iid reward vectors, for every round `t ∈ [T]` and
every action `a` that has been revealed at least once by the end of round `t`,
`|r̄^t_a − R_a| ≤ 3 √(log(2T) log(KT/δ) / n^t_a)`. The pair `K = T = 1` is excluded (`2 ≤ KT`). -/
theorem lemma_1 (K T : ℕ) (hKT : 2 ≤ K * T) (E : Fin K → Fin K → Prop) (hE : NoSelfLoops E)
    (P : Measure (Fin K → ℝ)) [IsProbabilityMeasure P]
    (hP : P {x | ∀ a, x a ∈ Set.Icc (0 : ℝ) 1}ᶜ = 0)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (opt : ArmOption) (tie : TieRule 1 K) (htie : IsTieRule tie) :
    (Measure.pi fun _ : Fin T => P)
      {r | ¬ ∀ t : Fin T, ∀ a : Fin K,
        1 ≤ (alg1State E opt tie T δ r (t.val + 1)).count a →
        |(alg1State E opt tie T δ r (t.val + 1)).empMean 0 a - meanRewardMAB P a| ≤
          3 * Real.sqrt (Real.log (2 * T) * Real.log (K * T / δ) /
            (alg1State E opt tie T δ r (t.val + 1)).count a)}
      ≤ ENNReal.ofReal δ := by sorry

end FirstPriceLearning.GraphFeedback
