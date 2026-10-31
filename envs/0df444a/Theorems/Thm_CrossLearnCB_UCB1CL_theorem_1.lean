-- Prove2me | Theorems.Thm_CrossLearnCB_UCB1CL_theorem_1
-- name    : CrossLearnCB.UCB1CL.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:36.259577+00:00
-- url     : https://prove2.me/theorems/8897c6fe-cdaf-4e67-90c4-e953e5b5dd88
-- title:
--   Theorem 1, p. 17 — UCB1.CL has E[Reg] ≤ 16 log T Σκ(G_i)/Δ* + Kπ²/3 and ≤ 17√(T log T Σκ(G_i)) + Kπ²/3
-- statement:
--   Consider the contextual bandit problem with cross-learning, with stochastic rewards and adversarial contexts. There are $K\ge1$ arms and $C\ge1$ contexts. The rewards $r_{i,t}(c)\in[0,1]$ are independent across rounds (arbitrarily correlated within a round), and $r_{i,t}(c)$ has a fixed law $\mathcal F_i(c)$ with mean $\mu_i(c)$; write $\mu^\star(c)=\max_i\mu_i(c)$ and $\Delta_i(c)=\mu^\star(c)-\mu_i(c)$. The contexts $c_1,c_2,\dots$ are an arbitrary sequence fixed in advance. Each arm $i$ has a cross-learning graph $G_i$ on the contexts with all self-loops, and $\kappa(G_i)$ is its clique covering number. Let $T\ge2$ and let $(I_t)$ be an arm process run by UCB1.CL (Algorithm 1), with ties broken by any non-anticipating rule. Write $\bar\kappa=\frac1K\sum_{i=1}^K\kappa(G_i)$ and $\mathrm{Reg}=\sum_{t=1}^T\Delta_{I_t}(c_t)$. Then:
--
--   1. (gap-dependent) for every $\Delta^*>0$ with $\Delta^*\le\Delta_i(c)$ whenever $\Delta_i(c)>0$,
--   $$\mathbb E[\mathrm{Reg}]\le\frac{16\log T}{\Delta^*}\sum_{i=1}^K\kappa(G_i)+\frac{K\pi^2}{3}=O\Big(\frac{K\bar\kappa\log T}{\Delta^*}\Big);$$
--   2. (gap-independent)
--   $$\mathbb E[\mathrm{Reg}]\le17\sqrt{T\log T\sum_{i=1}^K\kappa(G_i)}+\frac{K\pi^2}{3}=O\big(\sqrt{\bar\kappa KT\log T}\big).$$
--
--   With complete cross-learning ($\kappa(G_i)=1$) the regret is $O(\sqrt{KT\log T})$, independent of the number of contexts; with no cross-learning ($\kappa(G_i)=C$) it is $O(\sqrt{KCT\log T})$, the bound of running a separate UCB1 per context.
--
--   **Formalization Note.** The constants are those of the paper's proof: 16 from Lemma 3, $K\pi^2/3$ from Lemma 4, and $17=1+16$ from the choice $\Delta_{\min}=\sqrt{\bar\kappa K\log T/T}$ on p. 20. Three printed slips are repaired. (i) As printed, $\Delta^*=\min_{i,c}(\mu^\star(c)-\mu_i(c))$ includes the optimal arms and is $0$, so "$\Delta^*>0$" can never hold; $\Delta^*$ is posed as a positive lower bound on the positive gaps, which is what the proof uses. (ii) Display (5) carries an extra factor $K$; Lemma 3's constant, which matches the $O(K\bar\kappa\log T/\Delta^*)$ of the theorem, is used. (iii) $T\ge2$ is added (at $T=1$, $\log T=0$). The regret is the expected pseudo-regret of p. 17; it equals the expected realised regret because $I_t$ does not depend on round $t$'s rewards. Contexts are an oblivious deterministic sequence, so the bound holds for each sequence. The arm of round $t$ is required to be a measurable function of the rewards of earlier rounds, which makes the expectation meaningful and keeps tie-breaking non-anticipating.
-- source:
--   Balseiro et al., Contextual Bandits with Cross-Learning, arXiv:1809.09582v3, p. 17, Theorem 1; p. 20, (5) and the gap-independent bound

import Mathlib
import Definitions.Def_CrossLearnCB_UCB1CL_Model

open MeasureTheory ProbabilityTheory

namespace CrossLearnCB.UCB1CL

/-- Theorem 1, p. 17 (with the constants of its proof, (5) and p. 20): UCB1.CL with stochastic
rewards and an oblivious adversarial context sequence has expected pseudo-regret at most
`16 log T Σ_i κ(G_i) / Δ* + K π² / 3` for every `Δ* > 0` below all positive gaps, and at most
`17 √(T log T Σ_i κ(G_i)) + K π² / 3`, for `T ≥ 2`. -/
theorem theorem_1 {K C : ℕ} [NeZero K] [NeZero C] {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (R : ℕ → Ω → Fin K → Fin C → ℝ)
    (hR : IsStochRewards P R) (G : Fin K → Fin C → Fin C → Prop) (hG : HasSelfLoops G)
    (ctx : ℕ → Fin C) (T : ℕ) (hT : 2 ≤ T) (I : ℕ → Ω → Fin K)
    (hI : IsUCB1CLProcess R T G ctx I) :
    (∀ Δs : ℝ, 0 < Δs → (∀ i c, 0 < gap P R i c → Δs ≤ gap P R i c) →
      ∫ ω, pseudoRegret (gap P R) ctx (fun s => I s ω) T ∂P
        ≤ 16 * Real.log T * (∑ i, (cliqueCoverNumber (G i) : ℝ)) / Δs + K * Real.pi ^ 2 / 3) ∧
    ∫ ω, pseudoRegret (gap P R) ctx (fun s => I s ω) T ∂P
      ≤ 17 * Real.sqrt (T * Real.log T * ∑ i, (cliqueCoverNumber (G i) : ℝ))
        + K * Real.pi ^ 2 / 3 := by sorry

end CrossLearnCB.UCB1CL
