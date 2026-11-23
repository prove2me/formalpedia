-- Prove2me | Theorems.Thm_CrossLearnCB_UCB1CL_Supplement_theorem_8
-- name    : CrossLearnCB.UCB1CL.Supplement.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T05:00:05.853703+00:00
-- url     : https://prove2.me/theorems/0ee05b1e-5693-4a4f-b40b-7972bd25f2a1
-- title:
--   Theorem 8, p. 42 — a stochastic-reward regret lower bound R transfers to adversarial rewards as R − √(T log(KT))
-- statement:
--   Fix $K \ge 1$ arms, $C$ contexts, a horizon $T$ and CL graphs $G_1,\dots,G_K$ with self-loops.
--
--   1. A **stochastic instance** is a context distribution $D$ and laws $F_i(c)$ on $[0,1]$ with means $\mu_i(c)$; contexts are i.i.d. $D$ and round vectors are independent and every reward $r_{i,t}(c)$ has law $F_i(c)$, allowing correlation within each round as in p. 9, footnote 3. Its regret is measured against $\pi_{\mathrm{Stoc}}(c) \in \arg\max_i \mu_i(c)$.
--   2. An **adversarial instance** is a context distribution $D$ and a (possibly randomized) reward table in $[0,1]$ chosen before the game, independently of the contexts and of the algorithm. Its regret is measured against $\pi_{\mathrm{Adv}}(c) \in \arg\max_i \sum_{t} r_{i,t}(c)$ for the realized table.
--
--   For every algorithm $A$ and every stochastic instance there is an adversarial instance (with the same $D$) such that
--
--   $$\mathbb E\Big[\sum_{t=1}^T \big(r_{\pi_{\mathrm{Adv}}(c_t),t}(c_t) - r_{I_t,t}(c_t)\big)\Big] \ \ge\ \mathbb E\Big[\sum_{t=1}^T \big(r_{\pi_{\mathrm{Stoc}}(c_t),t}(c_t) - r_{I_t,t}(c_t)\big)\Big] - \sqrt{T\log(KT)},$$
--
--   where on the left the expectation is over the contexts, the table and the algorithm, and on the right over the rewards, the contexts and the algorithm. Consequently, the paper's form holds: if every algorithm has regret at least $R$ on some stochastic instance, then every algorithm has regret at least $R - \sqrt{T\log(KT)}$ on some adversarial instance.
--
--   This lets regret lower bounds proved with stochastic rewards be used for adversarial rewards.
--
--   **Formalization Note** The expected benchmark rewards are written as $T\sum_c D(c)\max_i\mu_i(c)$ and $\mathbb E_{r}[\sum_c D(c)\max_i\sum_t r_{i,t}(c)]$ (law of total expectation over the contexts, as in the proof), so ties among arg-maxima do not matter. Algorithms are valid policies whose arm probabilities depend measurably on the observed record, so that the expectation over random rewards is defined. The logarithm is natural.
--
--   Differences from the source:
--   - generalization: if every A has regret ≥ R on some stochastic instance, then every A has regret ≥ R − √(T log(KT)) on some adversarial instance → for every A and every stochastic instance S there is an adversarial instance whose regret is at least the regret on S minus √(T log(KT)); reason: given A, applying it to the instance supplied by the hypothesis yields the printed conclusion
--   - reading: any algorithm → a valid policy whose arm probabilities are measurable functions of the observed record; reason: the expectations over random rewards that the statement refers to are defined only for such algorithms
--   - encoding: E[Σ_t r_{π_Stoc(c_t),t}(c_t)] and E[Σ_t r_{π_Adv(c_t),t}(c_t)] → T Σ_c D(c) max_i μ_i(c) and the table average of Σ_c D(c) max_i Σ_t r_{i,t}(c); reason: law of total expectation over the i.i.d. contexts, as on p. 42; maxima make ties irrelevant
--   - encoding: stochastic rewards with fixed coordinate laws F_i(c), allowing correlation across arms and contexts within a round (p. 9, footnote 3), and a randomized adversarial table → a product of round-vector laws with these marginals and an arbitrary probability law on tables with values a.s. in [0,1]; reason: independence across rounds and fixed marginals encode the complete source domain; within-round couplings may vary with time, and a fixed adversarial table is a point mass
--   - generalization: the conclusion supplies an adversarial instance → the adversarial instance has V.D = S.D; reason: the construction on p. 42 explicitly preserves D; forgetting this equality recovers the printed conclusion
-- source:
--   Balseiro et al., Contextual Bandits with Cross-Learning, arXiv:1809.09582v3, p. 42, Theorem 8; π_Stoc, π_Adv p. 41; proof pp. 42–43

import Mathlib
import Definitions.Def_CrossLearnCB_UCB1CL_Model
import Definitions.Def_CrossLearnCB_UCB1CL_Supplement_Protocol

namespace CrossLearnCB.UCB1CL.Supplement

/-- Theorem 8, p. 42 (per-instance form): for every algorithm `A` and every instance `S` with
stochastic rewards and contexts there is an instance with adversarial (possibly randomized,
oblivious) rewards and the same context distribution on which `A`'s expected regret against
`π_Adv` is at least its expected regret on `S` against `π_Stoc` minus `√(T log(KT))`. -/
theorem theorem_8 {K C : ℕ} [NeZero K] (T : ℕ) (G : Fin K → Fin C → Fin C → Prop)
    (hG : HasSelfLoops G) (A : Policy K C) (hA : A.IsValid) (hAm : A.IsMeasurable)
    (S : StochInstance K C) :
    ∃ V : AdvInstance K C T, V.D = S.D ∧
      stochRegret T G S A - Real.sqrt (T * Real.log (K * T)) ≤ advRegret G V A := by sorry

end CrossLearnCB.UCB1CL.Supplement
