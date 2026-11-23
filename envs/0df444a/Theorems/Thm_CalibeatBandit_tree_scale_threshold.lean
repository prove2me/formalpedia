-- Prove2me | Theorems.Thm_CalibeatBandit_tree_scale_threshold
-- name    : CalibeatBandit.tree_scale_threshold
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-23T17:40:26.951204+00:00
-- url     : https://prove2.me/theorems/76fd3823-047d-49c7-932e-4f2a53d967f7
-- title:
--   Scale conditions of the tree construction hold for $K=16\cdot2^h\ge K_0$ and $K\le N\le2K$
-- statement:
--   **Statement.** There is $K_0\ge32$ such that for every depth $h$ and every number of actions $N$ with
--
--   $$K_0\le K\le N\le2K,\qquad K=16\cdot2^h,$$
--
--   the parameters of the tree construction, namely $L=2^h$ leaves, $M=8L$ auxiliary actions, period length $r=16K^3$, horizon $T=Lr=K^4$, $H=h+1$ levels and bonus scale $\eta=\frac1{1000KH}$, satisfy both
--
--   $$L\Big(\frac rM+\eta\,r\sqrt{\frac r{6M}}\Big)\ \le\ \frac T{64H}$$
--
--   and
--
--   $$\frac{N^3}{8\cdot10^{10}(\log N)^6}\ \le\ \frac\eta{48}\cdot\frac T{368\,H^5}-N\cdot\frac\eta{16}\sqrt{2T\log(2N)} .$$
--
--   Here $\log$ is the natural logarithm.
--
--   **Role.** These are the two numerical conditions under which the analysis of the tree construction yields the lower bound of Theorem 4.1: an information estimate (the first inequality) and the numerical regret estimate (the second), whose left-hand side is the target rate $N^3/(8\cdot10^{10}(\log N)^6)$. Both hold for all large $K$ because $H\le2\log K$. The statement fixes one threshold $K_0$ that works for every $N\in[K,2K]$, which is what lets the lower bound cover every number of actions and not only the dyadic values $16\cdot2^h$.
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (STOC 2027 submission 1457), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1457.pdf, §4, pp. 13–21: the construction (pp. 13–15) and the proof of Theorem 4.1 (pp. 20–21). Intermediate statement of jasonhartline's accepted Lean proof of CalibeatBandit.theorem_4_1 (submission 0ae8d87e-4337-4d82-8722-8eeded8a7691).

import Definitions.Def_CalibeatBandit_hard_tree_environment
import Definitions.Def_CalibeatBandit_swapRegret

set_option autoImplicit false

open CalibeatBandit MeasureTheory Set Filter

theorem CalibeatBandit.tree_scale_threshold :
    ∃ K₀ : ℕ, 32 ≤ K₀ ∧ ∀ h N : ℕ,
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
          N * (η / 16 * Real.sqrt (2 * T * Real.log (2 * N)))) := by sorry
