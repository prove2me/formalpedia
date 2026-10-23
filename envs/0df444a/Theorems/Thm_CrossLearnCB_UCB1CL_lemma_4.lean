-- Prove2me | Theorems.Thm_CrossLearnCB_UCB1CL_lemma_4
-- name    : CrossLearnCB.UCB1CL.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:47.903829+00:00
-- url     : https://prove2.me/theorems/c6e302d6-2abd-4dd3-af23-d82c5389ac2c
-- title:
--   Lemma 4, p. 20 — E[Reg_Post] ≤ Kπ²/3 for UCB1.CL
-- statement:
--   In the stochastic contextual bandit with cross-learning (rewards in $[0,1]$, independent across rounds, with fixed laws $\mathcal F_i(c)$ of means $\mu_i(c)$; an oblivious context sequence; cross-learning graphs with self-loops; horizon $T\ge2$), let $(I_t)$ be an arm process run by UCB1.CL and let $\Delta_{\min}>0$. The expected post-regret satisfies
--   $$\mathbb E\big[\mathrm{Reg}_{\mathrm{Post}}\big]=\mathbb E\Big[\sum_{t=1}^T\Delta_{I_t}(c_t)\,\mathbb I\big(\Delta_{I_t}(c_t)\ge\Delta_{\min},\ \tau_{I_t,t}(c_t)>m_{I_t}(c_t)\big)\Big]\le\frac{K\pi^2}{3},$$
--   with $m_i(c)=8\log T/\Delta_i(c)^2$ and $\tau_{i,t}(c)$ the number of observations of arm $i$ in context $c$ before round $t$.
--
--   Together with Lemma 3 this splits the regret of UCB1.CL into a pre-regret controlled by the clique covering numbers and a post-regret bounded by a constant independent of $T$ and of the number of contexts.
--
--   **Formalization Note.** The condition $\Delta_i(c)\ge\Delta_{\min}$, suppressed on p. 17, is explicit; with $\Delta_{\min}>0$ it excludes the optimal arms, for which Lean's $m_i(c)=8\log T/0$ is $0$ instead of $+\infty$. The hypothesis $T\ge2$ is the standing one of the mission.
-- source:
--   Balseiro et al., Contextual Bandits with Cross-Learning, arXiv:1809.09582v3, p. 20, Lemma 4; proof App. C.1, pp. 45–46

import Mathlib
import Definitions.Def_CrossLearnCB_UCB1CL_Model

open MeasureTheory ProbabilityTheory

namespace CrossLearnCB.UCB1CL

/-- Lemma 4, p. 20: the expected post-regret of UCB1.CL is at most `K π² / 3`. -/
theorem lemma_4 {K C : ℕ} [NeZero K] [NeZero C] {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (R : ℕ → Ω → Fin K → Fin C → ℝ)
    (hR : IsStochRewards P R) (G : Fin K → Fin C → Fin C → Prop) (hG : HasSelfLoops G)
    (ctx : ℕ → Fin C) (T : ℕ) (hT : 2 ≤ T) (I : ℕ → Ω → Fin K)
    (hI : IsUCB1CLProcess R T G ctx I) (Δmin : ℝ) (hΔ : 0 < Δmin) :
    ∫ ω, regPost (gap P R) G ctx (fun s => I s ω) T Δmin ∂P ≤ K * Real.pi ^ 2 / 3 := by sorry

end CrossLearnCB.UCB1CL
