-- Prove2me | Theorems.Thm_CalibeatBandit_exists_hard_tree_environment
-- name    : CalibeatBandit.exists_hard_tree_environment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-23T17:39:35.049803+00:00
-- url     : https://prove2.me/theorems/c6ddea2b-92cb-4fba-abb7-b472f184b311
-- title:
--   Hard tree environment — a realization with $\mathbb E[\mathrm{SR}_T]\ge N^3/(8\cdot10^{10}(\log N)^6)$ at $T=K^4$
-- statement:
--   **Setting.** Fix a depth $h\ge1$ and write $K=16\cdot2^h$. The tree construction has $2^h$ leaves, $M=8\cdot2^h$ auxiliary actions, periods of length $r=16K^3$, horizon $T=2^hr=K^4$, $H=h+1$ levels and bonus scale $\eta=\frac1{1000KH}$; in round $t$ the active leaf is $\min(\lfloor t/r\rfloor,2^h-1)$. Let $N$ be the number of actions of the learner, with $K\le N\le2K$, and let $e$ be a bijection between the $N$ actions and the actions of the construction (two per tree node, the $M$ auxiliary ones, and $U$ further actions that never receive a bonus).
--
--   A randomized bandit learner is given by a probability space $(S,P)$ of private seeds and maps $\mathrm{pick}_t$ that send a seed and the rewards observed in rounds $0,\dots,t-1$ to the action of round $t$, jointly measurable in the seed and the observations.
--
--   An environment $\mathrm{env}$ consists of the hidden tables (a coin for every round, a coin for every tree node, a selected auxiliary action for every leaf) and a tape of base and threshold draws for $T$ rounds. It determines a deterministic reward sequence $y_t(i)=y_t^{\mathrm{env}}(i)$, $t<T$, by
--
--   $$y_t(i)=\frac18+\frac{Z_t}8+\frac\eta8\,Z_t(1-Z_t)\,\mathbf 1\big[U_{t,i}<u_t(i)\big],$$
--
--   where $u_t(i)$ is the bonus probability of action $i$ for the active leaf of round $t$.
--
--   **Statement.** Suppose $K_0\le K$, where $K_0$ is a number for which the two inequalities of the scale lemma hold for every depth $h'$ and every $N'$ with $K_0\le16\cdot2^{h'}\le N'\le2\cdot16\cdot2^{h'}$ (this is the hypothesis `hscale`; such a $K_0$ exists by the scale lemma). Then for every such learner there is an environment $\mathrm{env}$ with
--
--   $$\int_S\mathrm{SR}_T\big(y^{\mathrm{env}},I^{\mathrm{env}}(s)\big)\,dP(s)\ \ge\ \frac{N^3}{8\cdot10^{10}(\log N)^6},$$
--
--   where $I^{\mathrm{env}}_t(s)$ is the action the learner with seed $s$ plays in round $t$ against the rewards $y^{\mathrm{env}}$, and $\mathrm{SR}_T(y,I)=\max_{\sigma}\sum_{t<T}\big(y_t(\sigma(I_t))-y_t(I_t)\big)$ is the swap regret.
--
--   **Role.** This is the hard instance behind Theorem 4.1, stated for the realized rewards of the construction. The proof bounds the learner's expected swap regret under the product law of the environment from below and then takes an environment that does at least as well as the average. Because the statement names the reward sequence, a proof that uses it can exploit the structure of the rewards: Theorem 4.1 needs only that they lie in $[0,1]$ and that $T=K^4$, while the pricing lower bound (Theorem 5.2) embeds the same rewards in demand curves and uses their explicit form to show that those curves are non-increasing.
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (STOC 2027 submission 1457), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1457.pdf, §4, pp. 13–21: the construction (pp. 13–15) and the proof of Theorem 4.1 (pp. 20–21). Intermediate statement of jasonhartline's accepted Lean proof of CalibeatBandit.theorem_4_1 (submission 0ae8d87e-4337-4d82-8722-8eeded8a7691).

import Definitions.Def_CalibeatBandit_hard_tree_environment
import Definitions.Def_CalibeatBandit_swapRegret

set_option autoImplicit false

open CalibeatBandit MeasureTheory Set Filter

theorem CalibeatBandit.exists_hard_tree_environment {S : Type*} [MeasurableSpace S] (P : Measure S)
    [IsProbabilityMeasure P]
    {K₀ h N U : ℕ} (hh : 0 < h) (hKN : treeActionBudget h ≤ N) (hNK : N ≤ 2 * treeActionBudget h)
    (hK₀ : K₀ ≤ treeActionBudget h)
    (hscale : ∀ h N : ℕ,
      K₀ ≤ treeActionBudget h → treeActionBudget h ≤ N → N ≤ 2 * treeActionBudget h →
      let L := 2 ^ h
      let M : ℕ := 8 * L
      let r := treePeriodLength h
      let T := L * r
      let H := treeHeight h
      let η := treeBonusScale h
      ((L : ℝ) * ((r : ℝ) / M + η * r * Real.sqrt ((r : ℝ) / (6 * M))) ≤
        (T : ℝ) / (64 * H)) ∧
      ((N : ℝ) ^ 3 / (8 * 10 ^ 10 * (Real.log N) ^ 6) ≤
        η / 48 * ((T : ℝ) / (368 * H ^ 5)) -
          N * (η / 16 * Real.sqrt (2 * T * Real.log (2 * N)))))
    (e : Fin N ≃ TreeAction h (8 * 2 ^ h) U) (pick : (t : ℕ) → S → FeedbackHistory t → Fin N)
    (hm : ∀ t, Measurable (fun p : S × FeedbackHistory t => pick t p.1 p.2)) (anchor : Fin N) :
    let r := treePeriodLength h
    let T := 2 ^ h * r
    let active := blockLeaf h r
    let η := treeBonusScale h
    ∃ env : TreeEnvironment h (8 * 2 ^ h) N T,
      (N : ℝ) ^ 3 / (8 * 10 ^ 10 * (Real.log N) ^ 6) ≤
        ∫ s, swapRegret T (treeEnvironmentReward e active η env)
          (treeEnvironmentAction e active η (fun t => pick t s) anchor env) ∂P := by sorry
