-- Prove2me | Theorems.Thm_CalibeatBandit_tree_expected_selected_hits
-- name    : CalibeatBandit.tree_expected_selected_hits
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-23T18:38:18.339478+00:00
-- url     : https://prove2.me/theorems/8fefd123-11d6-4c29-a806-90df3b916174
-- title:
--   Lemma 4.8 — expected plays of the selected auxiliary actions are at most $L(r/M+\eta r\sqrt{r/(6M)})$
-- statement:
--   **Lemma 4.8.** Consider the tree construction with $L=2^h$ periods of length $r$, horizon $T=Lr$, $M\ge1$ auxiliary actions and bonus scale $0\le\eta<1$, and draw the environment (leaf coins, node coins, one selected auxiliary action $J_\ell$ per period, and the tape of base and threshold draws) from its product law. For every deterministic measurable bandit learner,
--
--   $$\mathbb E\Big[\sum_{t<T}\mathbf 1\big[I_t=s_{J_{\ell(t)}}\big]\Big]\ \le\ L\Big(\frac rM+\eta\,r\sqrt{\frac r{6M}}\Big),$$
--
--   where $I_t$ is the action played in round $t$ and $\ell(t)$ is the active leaf of round $t$.
--
--   **Role.** The left-hand side is the expected number of rounds in which the learner plays the selected auxiliary action of the current period, the quantity $\mathbb E\sum_\ell\sum_{t\in\mathcal T_\ell}q_t(s_{J_\ell})$ of the paper. With $M=K/2$, $r=16K^3$ and $\eta=\frac1{1000KH}$ the right-hand side is at most $T/(64H)$ for large $K$, which is the form in which the paper states the lemma. A randomized learner is covered by applying the statement for each value of its seed.
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (STOC 2027 submission 1457), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1457.pdf, Lemma 4.8, p. 17 (proof pp. 17–19). Statement taken from jasonhartline's accepted Lean proof of CalibeatBandit.theorem_4_1 (submission 0ae8d87e-4337-4d82-8722-8eeded8a7691).

import Definitions.Def_CalibeatBandit_hard_tree_analysis

set_option autoImplicit false

open CalibeatBandit Filter MeasureTheory Set InformationTheory ProbabilityTheory
open scoped Interval ENNReal BigOperators

theorem CalibeatBandit.tree_expected_selected_hits {h M U N r : ℕ} [Nonempty (Fin M)]
    (e : Fin N ≃ TreeAction h M U) (η : ℝ) (hη : 0 ≤ η) (hη₁ : η < 1)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (hm : ∀ t, Measurable (pick t)) (anchor : Fin N) :
    let L := 2 ^ h
    let T := L * r
    let active := blockLeaf h r
    let P := treeEnvironmentLaw h M N T
    let q := treeEnvironmentPlay (T := T) e active η pick anchor
    (∫ env, ∑ t ∈ Finset.range T, q env t (treeAuxAction e (env.1.2.2 (active t))) ∂P) ≤
      (L : ℝ) * ((r : ℝ) / M + η * r * Real.sqrt ((r : ℝ) / (6 * M))) := by sorry
