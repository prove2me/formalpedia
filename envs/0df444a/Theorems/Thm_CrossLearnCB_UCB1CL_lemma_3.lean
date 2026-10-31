-- Prove2me | Theorems.Thm_CrossLearnCB_UCB1CL_lemma_3
-- name    : CrossLearnCB.UCB1CL.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:23.427897+00:00
-- url     : https://prove2.me/theorems/6b092803-d725-48c4-9c38-2e0fc60d5871
-- title:
--   Lemma 3, p. 18 — Reg_Pre ≤ 16 log T Σ_i κ(G_i)/Δ_min for every arm sequence (T ≥ 2)
-- statement:
--   Let $T\ge2$, let $G_1,\dots,G_K$ be cross-learning graphs on $[C]$ containing all self-loops, let the gaps $\Delta_i(c)$ be any numbers in $[0,1]$, and let $\Delta_{\min}>0$. For every context sequence $c_1,\dots,c_T$ and every arm sequence $I_1,\dots,I_T$, the pre-regret
--   $$\mathrm{Reg}_{\mathrm{Pre}}=\sum_{t=1}^T\Delta_{I_t}(c_t)\,\mathbb I\big(\Delta_{I_t}(c_t)\ge\Delta_{\min},\ \tau_{I_t,t}(c_t)\le m_{I_t}(c_t)\big),\qquad m_i(c)=\frac{8\log T}{\Delta_i(c)^2},$$
--   satisfies
--   $$\mathrm{Reg}_{\mathrm{Pre}}\le\frac{16\log T}{\Delta_{\min}}\sum_{i=1}^K\kappa(G_i),$$
--   where $\tau_{i,t}(c)$ is the number of observations of arm $i$ in context $c$ before round $t$ and $\kappa(G_i)$ is the clique covering number of $G_i$.
--
--   This is the main technical contribution of the analysis of UCB1.CL: the regret incurred while an arm is still under-observed in a context scales with the number of cliques needed to cover each cross-learning graph, not with the number of contexts.
--
--   **Formalization Note.** The paper states the bound for $\mathbb E[\mathrm{Reg}_{\mathrm{Pre}}]$, but its proof ends with the pathwise inequality (p. 20) and never uses the algorithm or the randomness; the expectation bound follows by integrating. The hypothesis $T\ge2$ is added: at $T=1$ the right side is $0$ while one round can carry regret. The condition $\Delta_i(c)\ge\Delta_{\min}$, suppressed on p. 17, is explicit in the indicator. The gaps are an arbitrary function with values in $[0,1]$; for the bandit model they are $\mu^\star(c)-\mu_i(c)$, which lies in $[0,1]$ because rewards do.
-- source:
--   Balseiro et al., Contextual Bandits with Cross-Learning, arXiv:1809.09582v3, p. 18, Lemma 3; pathwise form p. 20 (end of the proof of Lemma 3)

import Mathlib
import Definitions.Def_CrossLearnCB_UCB1CL_Model

open MeasureTheory ProbabilityTheory

namespace CrossLearnCB.UCB1CL

/-- Lemma 3, p. 18, in the pathwise form of its proof's last display (p. 20): for every arm
sequence and context sequence, `Reg_Pre ≤ 16 log T (Σ_i κ(G_i)) / Δ_min`, for `T ≥ 2`. -/
theorem lemma_3 {K C : ℕ} (gap : Fin K → Fin C → ℝ) (hgap : ∀ i c, gap i c ∈ Set.Icc (0 : ℝ) 1)
    (G : Fin K → Fin C → Fin C → Prop) (hG : HasSelfLoops G) (ctx : ℕ → Fin C) (I : ℕ → Fin K)
    (T : ℕ) (hT : 2 ≤ T) (Δmin : ℝ) (hΔ : 0 < Δmin) :
    regPre gap G ctx I T Δmin
      ≤ 16 * Real.log T * (∑ i, (cliqueCoverNumber (G i) : ℝ)) / Δmin := by sorry

end CrossLearnCB.UCB1CL
