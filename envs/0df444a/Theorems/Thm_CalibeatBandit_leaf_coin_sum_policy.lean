-- Prove2me | Theorems.Thm_CalibeatBandit_leaf_coin_sum_policy
-- name    : CalibeatBandit.leaf_coin_sum_policy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-23T18:41:43.289559+00:00
-- url     : https://prove2.me/theorems/035258f1-8330-4a70-aff0-ff9d68ea63cd
-- title:
--   Lemma 4.5 — leaf actions: $\mathbb E[G_i]\ge\mathbb E[Q_i]/(8H)$, summed over the leaf coins
-- statement:
--   **Setting.** Consider the tree construction of depth $h\ge1$ over $T$ rounds, with $H=h+1$, a deterministic learner whose actions are the tree actions, and fixed node coins, selected auxiliary actions, base draws and threshold draws. Let $v$ be a leaf of the tree and $i$ one of its two actions. For a sequence of leaf coins $c\in\{0,1\}^T$ let $q^c_t(i)\in\{0,1\}$ indicate that the learner plays $i$ in round $t$ when the leaf coins are $c$, let $u^c_t$ be the bonus probabilities, $Q_i(c)=\sum_{t<T}q^c_t(i)$ and $G_i(c)=\max_j\sum_{t<T}q^c_t(i)\big(u^c_t(j)-u^c_t(i)\big)$.
--
--   **Statement.**
--
--   $$\frac1{8H}\sum_{c\in\{0,1\}^T}Q_i(c)\ \le\ \sum_{c\in\{0,1\}^T}G_i(c).$$
--
--   **Role.** Dividing by $2^T$ gives Lemma 4.5 of the paper, $\mathbb E[G_i]\ge\mathbb E[Q_i]/(8H)$ for a leaf action, the expectation being over the fresh leaf coin of every round. The comparison actions are the selected auxiliary action, whose bonus probability is $1$, and the two root actions; the leaf coin of the current round is independent of the learner's action in that round, so a leaf action has the bonus only half of the time it is played.
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (STOC 2027 submission 1457), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1457.pdf, Lemma 4.5, p. 15 (proof pp. 15–16). Statement taken from jasonhartline's accepted Lean proof of CalibeatBandit.theorem_4_1 (submission 0ae8d87e-4337-4d82-8722-8eeded8a7691).

import Definitions.Def_CalibeatBandit_hard_tree_analysis

set_option autoImplicit false

open CalibeatBandit Filter MeasureTheory Set InformationTheory ProbabilityTheory
open scoped Interval ENNReal BigOperators

theorem CalibeatBandit.leaf_coin_sum_policy {h M U N T : ℕ} (hh : 0 < h) (e : Fin N ≃ TreeAction h M U)
    (v : TreeNode h) (hv : (v.1 : ℕ) = h) (side : Bool)
    (pick : (t : ℕ) → FeedbackHistory t → TreeAction h M U)
    (active : ℕ → Fin (2 ^ h)) (η : ℝ) (coin : TreeNode h → Bool)
    (selected : Fin (2 ^ h) → Fin M) (z : ℕ → Icc (0 : ℝ) 1)
    (draw : ℕ → TreeAction h M U → Ico (0 : ℝ) 1) :
    let leafCoin (c : Fin T → Bool) (t : ℕ) := if ht : t < T then c ⟨t, ht⟩ else false
    let i := e.symm (.inl (v, side))
    let q (c : Fin T → Bool) := treePlayProbability e pick active η coin (leafCoin c) selected z draw
    let u (c : Fin T → Bool) (t : ℕ) (j : Fin N) :=
      treeBonusProb (active t) coin (leafCoin c t) (selected (active t)) (e j)
    (∑ c, ∑ t ∈ Finset.range T, q c t i) / (8 * treeHeight h) ≤
      ∑ c, bestSwapGain T (q c) (u c) i := by sorry
