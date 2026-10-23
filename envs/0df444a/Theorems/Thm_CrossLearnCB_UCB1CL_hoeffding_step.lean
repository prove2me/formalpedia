-- Prove2me | Theorems.Thm_CrossLearnCB_UCB1CL_hoeffding_step
-- name    : CrossLearnCB.UCB1CL.hoeffding_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:31.899976+00:00
-- url     : https://prove2.me/theorems/1016f673-98f9-4ae0-a0b6-12d4deb43067
-- title:
--   p. 46, proof of Lemma 4 — Pr[x̄_{i,n}(c) ≤ μ_i(c) − ω(n)] and Pr[x̄_{i,n}(c) ≥ μ_i(c) + ω(n)] are at most exp(−4 log T)
-- statement:
--   Consider the stochastic contextual bandit with cross-learning: rewards $r_{i,t}(c)\in[0,1]$ independent across rounds with fixed laws $\mathcal F_i(c)$ of means $\mu_i(c)$, an oblivious context sequence, cross-learning graphs with self-loops, a horizon $T\ge2$, and an arm process $(I_t)$ run by UCB1.CL. Fix an arm $i$, a context $c$ and $n\ge1$, let $\bar x_{i,n}(c)$ be the average of the first $n$ rewards of arm $i$ in context $c$ observed by the algorithm, and let $\omega(n)=\sqrt{2\log T/n}$. Then
--   $$\Pr\big[\tau_{i,T+1}(c)\ge n,\ \bar x_{i,n}(c)\le\mu_i(c)-\omega(n)\big]\le e^{-4\log T},\qquad \Pr\big[\tau_{i,T+1}(c)\ge n,\ \bar x_{i,n}(c)\ge\mu_i(c)+\omega(n)\big]\le e^{-4\log T},$$
--   where $\tau_{i,T+1}(c)\ge n$ says that the $n$-th observation happens within the $T$ rounds.
--
--   This is the concentration step of the analysis of UCB1.CL: since $2n\,\omega(n)^2=4\log T$, Hoeffding's inequality gives the bound $T^{-4}$. The observations are taken at random rounds chosen by the algorithm, so the step is Hoeffding's inequality for a sample collected by an adaptive (optional-skipping) rule rather than for a fixed sample.
--
--   **Formalization Note.** The paper applies the lower tail to the optimal arm $i^\star(c_t)$ and the upper tail to arm $i$; one generic statement covers both. The paper uses $\bar x_{i,n}$ only when at least $n$ observations have been made; the statement is restricted to the event that the $n$-th observation occurs before the horizon. The paper's final $\le t^{-4}$ uses $t\le T$; the statement gives $e^{-4\log T}=T^{-4}$. Logarithms are natural.
-- source:
--   Balseiro et al., Contextual Bandits with Cross-Learning, arXiv:1809.09582v3, p. 46, proof of Lemma 4 (App. C.1); events 1–2 and x̄_{i,n}(c) p. 45

import Mathlib
import Definitions.Def_CrossLearnCB_UCB1CL_Model

open MeasureTheory ProbabilityTheory

namespace CrossLearnCB.UCB1CL

/-- Hoeffding step, p. 46 (proof of Lemma 4): the average `x̄_{i,n}(c)` of the first `n`
observed rewards of arm `i` in context `c` under UCB1.CL deviates below `μ_i(c) - ω(n)` or above
`μ_i(c) + ω(n)` with probability at most `exp(-4 log T)`, on the event that the `n`-th observation
happens within the horizon. -/
theorem hoeffding_step {K C : ℕ} [NeZero K] [NeZero C] {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (R : ℕ → Ω → Fin K → Fin C → ℝ)
    (hR : IsStochRewards P R) (G : Fin K → Fin C → Fin C → Prop) (hG : HasSelfLoops G)
    (ctx : ℕ → Fin C) (T : ℕ) (hT : 2 ≤ T) (I : ℕ → Ω → Fin K)
    (hI : IsUCB1CLProcess R T G ctx I) (i : Fin K) (c : Fin C) (n : ℕ) (hn : 1 ≤ n) :
    P {ω | n ≤ obsCount G ctx (fun s => I s ω) T i c ∧
        firstNMean G ctx (fun s => I s ω) (fun s => R s ω) i c n
          ≤ mu P R i c - Real.sqrt (2 * Real.log T / n)}
        ≤ ENNReal.ofReal (Real.exp (-4 * Real.log T)) ∧
    P {ω | n ≤ obsCount G ctx (fun s => I s ω) T i c ∧
        mu P R i c + Real.sqrt (2 * Real.log T / n)
          ≤ firstNMean G ctx (fun s => I s ω) (fun s => R s ω) i c n}
        ≤ ENNReal.ofReal (Real.exp (-4 * Real.log T)) := by sorry

end CrossLearnCB.UCB1CL
