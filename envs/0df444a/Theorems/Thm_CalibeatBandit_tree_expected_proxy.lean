-- Prove2me | Theorems.Thm_CalibeatBandit_tree_expected_proxy
-- name    : CalibeatBandit.tree_expected_proxy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-23T18:39:35.326858+00:00
-- url     : https://prove2.me/theorems/b9d6b98e-07ea-49f4-ae1a-e874c03b691f
-- title:
--   Lemma 4.9 — total expected swap gain $\mathbb E[G]\ge T/(368H^5)$
-- statement:
--   **Lemma 4.9.** Consider the tree construction of depth $h\ge1$ with $L=2^h$ periods of length $r$, horizon $T=Lr$, $M\ge1$ auxiliary actions, $H=h+1$ and bonus scale $0\le\eta<1$, and suppose
--
--   $$L\Big(\frac rM+\eta\,r\sqrt{\frac r{6M}}\Big)\ \le\ \frac T{64H}.$$
--
--   Draw the environment from its product law. For every deterministic measurable bandit learner, with $q_t$ the indicator vector of the action played in round $t$ and $u_t$ the bonus probabilities,
--
--   $$\mathbb E\big[G\big]\ \ge\ \frac T{368H^5},\qquad G=\max_\sigma\sum_{t<T}\sum_iq_t(i)\big(u_t(\sigma(i))-u_t(i)\big)=\sum_i\max_j\sum_{t<T}q_t(i)\big(u_t(j)-u_t(i)\big).$$
--
--   **Role.** $G$ is the total swap gain measured in bonus probabilities. The hypothesis is the first scale inequality of the construction; it is the conclusion of Lemma 4.8 in the form $\mathbb E\sum_t q_t(s_{J_{\ell(t)}})\le T/(64H)$. The lemma is the lower bound that the martingale argument of the proof of Theorem 4.1 converts into a swap-regret lower bound.
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (STOC 2027 submission 1457), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1457.pdf, Lemma 4.9, p. 20. Statement taken from jasonhartline's accepted Lean proof of CalibeatBandit.theorem_4_1 (submission 0ae8d87e-4337-4d82-8722-8eeded8a7691).

import Definitions.Def_CalibeatBandit_hard_tree_analysis

set_option autoImplicit false

open CalibeatBandit Filter MeasureTheory Set InformationTheory ProbabilityTheory
open scoped Interval ENNReal BigOperators

theorem CalibeatBandit.tree_expected_proxy {h M U N r : ℕ} [Nonempty (Fin M)] (hh : 0 < h)
    (e : Fin N ≃ TreeAction h M U) (η : ℝ) (hη : 0 ≤ η) (hη₁ : η < 1)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (hm : ∀ t, Measurable (pick t)) (anchor : Fin N)
    (hbudget : ((2 ^ h : ℕ) : ℝ) * ((r : ℝ) / M + η * r * Real.sqrt ((r : ℝ) / (6 * M))) ≤
      ((2 ^ h * r : ℕ) : ℝ) / (64 * treeHeight h)) :
    let T := 2 ^ h * r
    let active := blockLeaf h r
    let P := treeEnvironmentLaw h M N T
    let q := treeEnvironmentPlay (T := T) e active η pick anchor
    (T : ℝ) / (368 * treeHeight h ^ 5) ≤
      ∫ env, pseudoSwapRegret T (q env) (tableBonuses e active env.1) ∂P := by sorry
