-- Prove2me | Theorems.Thm_CrossLearnCB_UCB1CL_per_round_bound
-- name    : CrossLearnCB.UCB1CL.per_round_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:40.309949+00:00
-- url     : https://prove2.me/theorems/ed75586b-fc4e-468d-9145-9a6ab1d1e23d
-- title:
--   p. 46, proof of Lemma 4 — Pr[I_t = i, τ_{i,t}(c_t) > m_i(c_t)] ≤ 2t^{−2} for a suboptimal arm
-- statement:
--   In the stochastic contextual bandit with cross-learning (rewards in $[0,1]$, independent across rounds, with fixed laws of means $\mu_i(c)$; an oblivious context sequence; cross-learning graphs with self-loops; horizon $T\ge2$), let $(I_t)$ be an arm process run by UCB1.CL. For every round $t\le T$ and every arm $i$ with positive gap $\Delta_i(c_t)>0$ in the context of that round,
--   $$\Pr\big[I_t=i,\ \tau_{i,t}(c_t)>m_i(c_t)\big]\le\frac{2}{t^{2}},\qquad m_i(c)=\frac{8\log T}{\Delta_i(c)^2},$$
--   where $\tau_{i,t}(c_t)$ is the number of observations of arm $i$ in context $c_t$ before round $t$.
--
--   Summing this bound over arms and rounds gives Lemma 4: once an arm has been observed $m_i(c)$ times in a context, UCB1.CL pulls it there only with small probability.
--
--   **Formalization Note.** Lean's rounds are 0-based: Lean's round $t<T$ is the paper's round $t+1$, so the bound reads $2/(t+1)^2$. The positivity of the gap is required: for an optimal arm the page's $m_i(c)=+\infty$ but Lean's $8\log T/0=0$, and the bound would be false.
-- source:
--   Balseiro et al., Contextual Bandits with Cross-Learning, arXiv:1809.09582v3, p. 46, proof of Lemma 4 (App. C.1)

import Mathlib
import Definitions.Def_CrossLearnCB_UCB1CL_Model

open MeasureTheory ProbabilityTheory

namespace CrossLearnCB.UCB1CL

/-- Per-round bound, p. 46 (proof of Lemma 4): for a suboptimal arm `i` in the context of
0-based round `t < T` (the paper's round `t + 1`),
`Pr[I_t = i, τ_{i,t}(c_t) > m_i(c_t)] ≤ 2 (t + 1)^{-2}`. -/
theorem per_round_bound {K C : ℕ} [NeZero K] [NeZero C] {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (R : ℕ → Ω → Fin K → Fin C → ℝ)
    (hR : IsStochRewards P R) (G : Fin K → Fin C → Fin C → Prop) (hG : HasSelfLoops G)
    (ctx : ℕ → Fin C) (T : ℕ) (hT : 2 ≤ T) (I : ℕ → Ω → Fin K)
    (hI : IsUCB1CLProcess R T G ctx I) (t : ℕ) (ht : t < T) (i : Fin K)
    (hi : 0 < gap P R i (ctx t)) :
    P {ω | I t ω = i ∧
        mThr T (gap P R i (ctx t)) < (obsCount G ctx (fun s => I s ω) t i (ctx t) : ℝ)}
      ≤ ENNReal.ofReal (2 / ((t : ℝ) + 1) ^ 2) := by sorry

end CrossLearnCB.UCB1CL
