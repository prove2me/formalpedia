-- Prove2me | Theorems.Thm_FirstPriceLearning_GraphFeedback_theorem_3
-- name    : FirstPriceLearning.GraphFeedback.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:28:38.655714+00:00
-- url     : https://prove2.me/theorems/6e9d64d9-899f-4622-85cc-033fae713a12
-- title:
--   Theorem 3 — Algorithm 1 has regret T ∧ Õ(√(αT log(1/δ))) with probability 1 − δ
-- statement:
--   Consider a stochastic multi-armed bandit with graph feedback (Definition 1): actions $\mathcal A = [K]$ with $K \ge 1$, a feedback graph $G = (\mathcal A, E)$ without self-loops whose independence number is at most $\alpha$, and iid reward vectors from a law $P$ on $[0,1]^K$ with mean rewards $R_a$. Let $\delta \in (0,1)$ and let $R_T(\pi)$ be the regret (4) of Algorithm 1.
--
--   1. **Option I (any graph).** For every admissible tie-breaking rule, with probability at least $1-\delta$,
--   $$
--   R_T(\pi) \le T \wedge \Big(50\alpha(\log K)^2 + 24\log K\cdot\sqrt{50\alpha T\log(2T)\log(KT/\delta)}\Big).
--   $$
--   2. **Option II (DAG).** If $G$ is a directed acyclic graph, then for every admissible tie-breaking rule, with probability at least $1-\delta$,
--   $$
--   R_T(\pi) \le T \wedge \Big(\alpha + 24\sqrt{\alpha T\log(2T)\log(KT/\delta)}\Big).
--   $$
--
--   Here $x \wedge y = \min\{x,y\}$ and $\log$ is the natural logarithm. With $\delta = 1/T$ the theorem gives an expected regret $\tilde O(\sqrt{\alpha T})$, which is optimal up to logarithmic factors; Theorem 4 extends it to contexts with cross learning.
--
--   **Formalization Note** Algorithm 1 is Algorithm 2 with one context (see the definition module). For $K = 1$ the Option I bound is $0$, which is correct since a single action has no regret. The $\tilde O(\cdot)$ tail of the printed statement is not formalized. The probability is over the iid rewards; the bad event's outer measure under $P^{\otimes T}$ is at most $\delta$.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 13, Theorem 3 (proof: pp. 13–14)

import Mathlib
import Definitions.Def_FirstPriceLearning_GraphFeedback_FeedbackGraph
import Definitions.Def_FirstPriceLearning_GraphFeedback_BanditModel
import Definitions.Def_FirstPriceLearning_GraphFeedback_ArmElimination

open MeasureTheory

namespace FirstPriceLearning.GraphFeedback

/-- Theorem 3 (p. 13): for a stochastic multi-armed bandit with feedback graph `E` (no self-loops,
independence number at most `α`) and rewards in `[0,1]`, with probability at least `1 − δ`
Algorithm 1 has regret (4) at most
`T ∧ (50α(log K)² + 24 log K · √(50αT log(2T) log(KT/δ)))` with Option I (any graph, any
admissible tie-breaking rule), and at most `T ∧ (α + 24 √(αT log(2T) log(KT/δ)))` with Option II
when `E` is a DAG. -/
theorem theorem_3 (K T α : ℕ) (hK : 1 ≤ K) (E : Fin K → Fin K → Prop) (hE : NoSelfLoops E)
    (hα : IndepNumberLE E α)
    (P : Measure (Fin K → ℝ)) [IsProbabilityMeasure P]
    (hP : P {x | ∀ a, x a ∈ Set.Icc (0 : ℝ) 1}ᶜ = 0)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (∀ tie : TieRule 1 K, IsTieRule tie →
      (Measure.pi fun _ : Fin T => P)
        {r | ¬ regretMAB (meanRewardMAB P) (alg1Action E .optionI tie T δ r) ≤
          min (T : ℝ) (50 * α * Real.log K ^ 2 + 24 * Real.log K *
            Real.sqrt (50 * α * T * Real.log (2 * T) * Real.log (K * T / δ)))}
        ≤ ENNReal.ofReal δ) ∧
    (IsDAG E → ∀ tie : TieRule 1 K, IsTieRule tie →
      (Measure.pi fun _ : Fin T => P)
        {r | ¬ regretMAB (meanRewardMAB P) (alg1Action E .optionII tie T δ r) ≤
          min (T : ℝ) (α + 24 *
            Real.sqrt (α * T * Real.log (2 * T) * Real.log (K * T / δ)))}
        ≤ ENNReal.ofReal δ) := by sorry

end FirstPriceLearning.GraphFeedback
