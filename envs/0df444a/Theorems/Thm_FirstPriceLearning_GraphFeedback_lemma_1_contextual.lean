-- Prove2me | Theorems.Thm_FirstPriceLearning_GraphFeedback_lemma_1_contextual
-- name    : FirstPriceLearning.GraphFeedback.lemma_1_contextual
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:28:34.653782+00:00
-- url     : https://prove2.me/theorems/16fb239d-52e3-4515-943e-7f5e8c1febff
-- title:
--   Proof of Theorem 4 — Lemma 1 for Algorithm 2 with δ replaced by δ/M, for all contexts
-- statement:
--   Consider a stochastic contextual bandit with graph feedback and cross learning (Definition 2): contexts $\mathcal C = [M]$, actions $\mathcal A = [K]$, a feedback graph without self-loops, and iid reward vectors from a law $P$ on $[0,1]^{M\times K}$ with mean rewards $R_{c,a}$. Fix any context sequence $c_1, \dots, c_T$ and run Algorithm 2 with either option, any admissible tie-breaking rule and failure probability $\delta \in (0,1)$. Write $n^t_a$ for the number of rounds $s \le t$ in which action $a$ was revealed and $\bar r^t_{c,a}$ for the mean of the rewards $r_{s,c,a}$ over those rounds. Assume $MKT \ge 2$.
--
--   Then, with probability at least $1-\delta$,
--   $$
--   \big|\bar r^t_{c,a} - R_{c,a}\big| \le 3\sqrt{\frac{\log(2T)\log(MKT/\delta)}{n^t_a}}
--   $$
--   for every $t \in [T]$, every $c \in \mathcal C$ and every $a \in \mathcal A$ with $n^t_a \ge 1$.
--
--   This is the first step of the proof of Theorem 4: Lemma 1 with $\delta$ replaced by $\delta/M$, made uniform over the contexts by a union bound.
--
--   **Formalization Note** As for Lemma 1, the statement quantifies over $n^t_a \ge 1$, and the degenerate case $M = K = T = 1$ (where the bound fails for $\delta$ close to $1$) is excluded. The context sequence is fixed in advance (oblivious); the probability is the outer measure under $P^{\otimes T}$.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 16, proof of Theorem 4, first sentence

import Mathlib
import Definitions.Def_FirstPriceLearning_GraphFeedback_FeedbackGraph
import Definitions.Def_FirstPriceLearning_GraphFeedback_BanditModel
import Definitions.Def_FirstPriceLearning_GraphFeedback_ArmElimination

open MeasureTheory

namespace FirstPriceLearning.GraphFeedback

/-- The contextual form of Lemma 1 (proof of Theorem 4, p. 16), for Algorithm 2 with either
option, any admissible tie-breaking rule and any fixed context sequence: with probability at
least `1 − δ`, for every round `t ∈ [T]`, context `c` and action `a` revealed at least once by
the end of round `t`, `|r̄^t_{c,a} − R_{c,a}| ≤ 3 √(log(2T) log(MKT/δ) / n^t_a)`. The case
`M = K = T = 1` is excluded (`2 ≤ MKT`). -/
theorem lemma_1_contextual (M K T : ℕ) (hMKT : 2 ≤ M * K * T) (E : Fin K → Fin K → Prop)
    (hE : NoSelfLoops E)
    (P : Measure (Fin M → Fin K → ℝ)) [IsProbabilityMeasure P]
    (hP : P {x | ∀ c a, x c a ∈ Set.Icc (0 : ℝ) 1}ᶜ = 0)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (ctx : Fin T → Fin M)
    (opt : ArmOption) (tie : TieRule M K) (htie : IsTieRule tie) :
    (Measure.pi fun _ : Fin T => P)
      {r | ¬ ∀ t : Fin T, ∀ c : Fin M, ∀ a : Fin K,
        1 ≤ (elimState E opt tie T δ ctx r (t.val + 1)).count a →
        |(elimState E opt tie T δ ctx r (t.val + 1)).empMean c a - meanReward P c a| ≤
          3 * Real.sqrt (Real.log (2 * T) * Real.log (M * K * T / δ) /
            (elimState E opt tie T δ ctx r (t.val + 1)).count a)}
      ≤ ENNReal.ofReal δ := by sorry

end FirstPriceLearning.GraphFeedback
