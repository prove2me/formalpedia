-- Prove2me | Theorems.Thm_FirstPriceLearning_GraphFeedback_theorem_4
-- name    : FirstPriceLearning.GraphFeedback.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:28:35.627004+00:00
-- url     : https://prove2.me/theorems/7e2e2915-0f58-409f-83fe-c0e1f68ce7fc
-- title:
--   Theorem 4 — Algorithm 2 has regret T ∧ Õ(√(αMT)) ∧ Õ(√(KT)) with probability 1 − δ
-- statement:
--   Consider a stochastic contextual bandit with graph feedback and cross learning (Definition 2): contexts $\mathcal C = [M]$ with $M \ge 1$, actions $\mathcal A = [K]$ with $K \ge 1$, a feedback graph $G = (\mathcal A, E)$ without self-loops whose independence number is at most $\alpha$, and iid reward vectors from a law $P$ on $[0,1]^{M\times K}$ with mean rewards $R_{c,a}$. Let $\delta \in (0,1)$, let $c_1, \dots, c_T$ be any context sequence, and let $R_T(\pi)$ be the regret (5) of Algorithm 2. Write $L = \log(2T)\log(MKT/\delta)$.
--
--   1. **Option I (any graph).** For every admissible tie-breaking rule, with probability at least $1-\delta$,
--   $$
--   R_T(\pi) \le T \wedge \Big(K + 24\sqrt{KT L}\Big) \wedge \Big(50\alpha M(\log K)^2 + 24\log K\cdot\sqrt{50\alpha M T L}\Big).
--   $$
--   2. **Option II (DAG).** If $G$ is a directed acyclic graph, then for every admissible tie-breaking rule, with probability at least $1-\delta$,
--   $$
--   R_T(\pi) \le T \wedge \Big(K + 24\sqrt{KT L}\Big) \wedge \Big(\alpha M + 24\sqrt{\alpha M T L}\Big).
--   $$
--
--   Here $x \wedge y = \min\{x,y\}$ and $\log$ is the natural logarithm. The second bound is what one gets by using the cross learning and ignoring the feedback graph, the third by using the feedback graph within each context and ignoring the cross learning; Algorithm 2 attains the better of the two simultaneously, so its regret is $\tilde O(T \wedge \sqrt{\alpha M T\log(1/\delta)} \wedge \sqrt{KT\log(1/\delta)})$.
--
--   **Formalization Note** The paper prints the second bound as $K + 3\sqrt{KT\log(2T)\log(MKT/\delta)}$. Its proof bounds each choice by $4\Delta(n)$ and then sums $1 + \Delta(1) + \dots + \Delta(T_a - 1)$, dropping the factor $4$; with the factor kept the same argument gives $24$, which is stated here. The theorem is stated for every fixed (oblivious) context sequence, which covers adversarial contexts and, by conditioning, stochastic contexts independent of the rewards. The $\tilde O(\cdot)$ tail is not formalized. The probability is the outer measure of the bad event under $P^{\otimes T}$.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, pp. 15–16, Theorem 4 (proof: p. 16)

import Mathlib
import Definitions.Def_FirstPriceLearning_GraphFeedback_FeedbackGraph
import Definitions.Def_FirstPriceLearning_GraphFeedback_BanditModel
import Definitions.Def_FirstPriceLearning_GraphFeedback_ArmElimination

open MeasureTheory

namespace FirstPriceLearning.GraphFeedback

/-- Theorem 4 (pp. 15–16), with the first bound's constant `24` (the printed `3` is not what the
printed proof gives): for a stochastic contextual bandit with feedback graph `E` (no self-loops,
independence number at most `α`), cross learning, rewards in `[0,1]` and any fixed context
sequence, with probability at least `1 − δ` Algorithm 2 has regret (5) at most
`T ∧ (K + 24 √(KT log(2T) log(MKT/δ))) ∧ (50αM(log K)² + 24 log K · √(50αMT log(2T) log(MKT/δ)))`
with Option I (any graph, any admissible tie-breaking rule), and at most
`T ∧ (K + 24 √(KT log(2T) log(MKT/δ))) ∧ (αM + 24 √(αMT log(2T) log(MKT/δ)))`
with Option II when `E` is a DAG. -/
theorem theorem_4 (M K T α : ℕ) (hM : 1 ≤ M) (hK : 1 ≤ K) (E : Fin K → Fin K → Prop)
    (hE : NoSelfLoops E) (hα : IndepNumberLE E α)
    (P : Measure (Fin M → Fin K → ℝ)) [IsProbabilityMeasure P]
    (hP : P {x | ∀ c a, x c a ∈ Set.Icc (0 : ℝ) 1}ᶜ = 0)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (ctx : Fin T → Fin M) :
    (∀ tie : TieRule M K, IsTieRule tie →
      (Measure.pi fun _ : Fin T => P)
        {r | ¬ regret P ctx (elimAction E .optionI tie T δ ctx r) ≤
          min (T : ℝ) (min
            (K + 24 * Real.sqrt (K * T * Real.log (2 * T) * Real.log (M * K * T / δ)))
            (50 * α * M * Real.log K ^ 2 + 24 * Real.log K *
              Real.sqrt (50 * α * M * T * Real.log (2 * T) * Real.log (M * K * T / δ))))}
        ≤ ENNReal.ofReal δ) ∧
    (IsDAG E → ∀ tie : TieRule M K, IsTieRule tie →
      (Measure.pi fun _ : Fin T => P)
        {r | ¬ regret P ctx (elimAction E .optionII tie T δ ctx r) ≤
          min (T : ℝ) (min
            (K + 24 * Real.sqrt (K * T * Real.log (2 * T) * Real.log (M * K * T / δ)))
            (α * M + 24 *
              Real.sqrt (α * M * T * Real.log (2 * T) * Real.log (M * K * T / δ))))}
        ≤ ENNReal.ofReal δ) := by sorry

end FirstPriceLearning.GraphFeedback
