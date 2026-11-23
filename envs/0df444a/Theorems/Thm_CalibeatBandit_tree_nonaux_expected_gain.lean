-- Prove2me | Theorems.Thm_CalibeatBandit_tree_nonaux_expected_gain
-- name    : CalibeatBandit.tree_nonaux_expected_gain
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-23T18:39:09.779747+00:00
-- url     : https://prove2.me/theorems/3df20d29-2264-4dc0-bc2c-0e30d768f253
-- title:
--   Lemmas 4.4–4.6 — every non-auxiliary action has $\mathbb E[G_i]\ge\mathbb E[Q_i]/(184H^5)$
-- statement:
--   **Lemmas 4.4–4.6.** Consider the tree construction of depth $h\ge1$ over $T$ rounds, with $H=h+1$, $M\ge1$ auxiliary actions and an active-leaf schedule that is non-decreasing in time, and draw the environment (leaf coins, node coins, selected auxiliary actions and the tape of draws) from its product law. For a deterministic measurable bandit learner let $q_t(i)\in\{0,1\}$ indicate that it plays action $i$ in round $t$, let $u_t$ be the bonus probabilities, $Q_i=\sum_{t<T}q_t(i)$ and $G_i=\max_j\sum_{t<T}q_t(i)\big(u_t(j)-u_t(i)\big)$. Then for every action $i$ that is not an auxiliary action,
--
--   $$\mathbb E[G_i]\ \ge\ \frac{\mathbb E[Q_i]}{184H^5}.$$
--
--   **Role.** This combines Lemma 4.4 (unnamed actions, with constant $4H$), Lemma 4.5 (leaf actions, $8H$) and Lemma 4.6 (internal node actions, $184H^5$) of the paper under the weakest of the three constants. It says that every round spent on a non-auxiliary action contributes to the expected swap gain, which is half of the case analysis in Lemma 4.9.
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (STOC 2027 submission 1457), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1457.pdf, Lemmas 4.4, 4.5 and 4.6, pp. 15–16. Statement taken from jasonhartline's accepted Lean proof of CalibeatBandit.theorem_4_1 (submission 0ae8d87e-4337-4d82-8722-8eeded8a7691).

import Definitions.Def_CalibeatBandit_hard_tree_analysis

set_option autoImplicit false

open CalibeatBandit Filter MeasureTheory Set InformationTheory ProbabilityTheory
open scoped Interval ENNReal BigOperators

theorem CalibeatBandit.tree_nonaux_expected_gain {h M U N T : ℕ} [Nonempty (Fin M)] (hh : 0 < h)
    (e : Fin N ≃ TreeAction h M U) (active : ℕ → Fin (2 ^ h)) (ha : Monotone active) (η : ℝ)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (hm : ∀ t, Measurable (pick t))
    (anchor i : Fin N) (hi : ∀ j, treeAuxAction e j ≠ i) :
    let P := treeEnvironmentLaw h M N T
    let q := treeEnvironmentPlay (T := T) e active η pick anchor
    let u (env : TreeEnvironment h M N T) := tableBonuses e active env.1
    (∫ env, ∑ t ∈ Finset.range T, q env t i ∂P) / (184 * treeHeight h ^ 5) ≤
      ∫ env, bestSwapGain T (q env) (u env) i ∂P := by sorry
