-- Prove2me | Theorems.Thm_CalibeatBandit_deepest_left_coin_sum_policy
-- name    : CalibeatBandit.deepest_left_coin_sum_policy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-23T18:44:28.465818+00:00
-- url     : https://prove2.me/theorems/fc14e664-f2c6-4e70-bf3b-c41feab0823a
-- title:
--   Lemma 4.6 — action $a_v$ of a node above the leaves: $\mathbb E[G_i]\ge\mathbb E[Q_i]/(184H^5)$, summed over the node coins
-- statement:
--   **Setting.** Consider the tree construction of depth $h$ over $T$ rounds, with $H=h+1$ and an active-leaf schedule that is non-decreasing in time. Fix a deterministic learner whose actions are the tree actions, the leaf coins, the selected auxiliary actions and the draws. Let $v$ be an internal node whose two children are leaves (depth $h-1$) and let $i=a_v$ be its first action. For an assignment $c$ of coins to the nodes let $q^c_t(i)\in\{0,1\}$ indicate that the learner plays $i$ in round $t$, let $u^c_t$ be the bonus probabilities, $Q_i(c)=\sum_{t<T}q^c_t(i)$ and $G_i(c)=\max_j\sum_{t<T}q^c_t(i)\big(u^c_t(j)-u^c_t(i)\big)$.
--
--   **Statement.**
--
--   $$\frac1{184H^5}\sum_{c}Q_i(c)\ \le\ \sum_{c}G_i(c),$$
--
--   the sums being over all assignments of coins to the nodes of the tree.
--
--   **Role.** Dividing by the number of assignments gives the case of Lemma 4.6 of the paper for the action $a_v$ of a node at the last internal level, where the comparison actions below $v$ are leaf actions: $\mathbb E[G_i]\ge\mathbb E[Q_i]/(184H^5)$.
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (STOC 2027 submission 1457), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1457.pdf, Lemma 4.6, p. 16 (proof in Appendix D), the case of the first action of a node whose children are leaves. Statement taken from jasonhartline's accepted Lean proof of CalibeatBandit.theorem_4_1 (submission 0ae8d87e-4337-4d82-8722-8eeded8a7691).

import Definitions.Def_CalibeatBandit_hard_tree_analysis

set_option autoImplicit false

open CalibeatBandit Filter MeasureTheory Set InformationTheory ProbabilityTheory
open scoped Interval ENNReal BigOperators

theorem CalibeatBandit.deepest_left_coin_sum_policy {h M U N T : ℕ} (e : Fin N ≃ TreeAction h M U)
    (v : TreeNode h) (hv : (v.1 : ℕ) + 1 = h)
    (pick : (t : ℕ) → FeedbackHistory t → TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (ha : Monotone active) (η : ℝ) (leafCoin : ℕ → Bool)
    (selected : Fin (2 ^ h) → Fin M) (z : ℕ → Icc (0 : ℝ) 1)
    (draw : ℕ → TreeAction h M U → Ico (0 : ℝ) 1) :
    let i := e.symm (.inl (v, false))
    let q (coin : TreeNode h → Bool) := treePlayProbability e pick active η coin leafCoin selected z draw
    let u (coin : TreeNode h → Bool) (t : ℕ) (j : Fin N) :=
      treeBonusProb (active t) coin (leafCoin t) (selected (active t)) (e j)
    (∑ c, ∑ t ∈ Finset.range T, q c t i) / (184 * treeHeight h ^ 5) ≤
      ∑ c, bestSwapGain T (q c) (u c) i := by sorry
