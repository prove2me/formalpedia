-- Prove2me | Theorems.Thm_CalibeatBandit_integral_periodHits_average_le
-- name    : CalibeatBandit.integral_periodHits_average_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-23T18:40:55.713385+00:00
-- url     : https://prove2.me/theorems/3965aaa3-6f8b-40f6-bfad-7e9d8eae7b54
-- title:
--   Proof of Lemma 4.8 — in one period the selected auxiliary action is played at most $r/M+\eta r\sqrt{r/(6M)}$ times on average
-- statement:
--   **Setting.** Consider one period of $r$ rounds of the tree construction with a fixed active leaf, fixed node coins and fixed leaf coins. For each candidate $j\in[M]$ let world $j$ be the reward process in which the auxiliary action $s_j$ is the selected one (bonus probability $1$) and the other auxiliary actions have bonus probability $0$. The base draws are uniform on $[0,1]$ and the threshold draws uniform on $[0,1)$, all independent, and $0\le\eta<1$ is the bonus scale. A deterministic learner chooses each action as a measurable function of the observations of the period so far, on the normalized scale $8y-1$ (an invertible change of the observed rewards).
--
--   **Statement.** Let $H_j$ be the number of rounds of the period in which the learner plays $s_j$ in world $j$. Then
--
--   $$\frac1M\sum_{j=1}^M\mathbb E\big[H_j\big]\ \le\ \frac rM+\eta\,r\sqrt{\frac r{6M}} .$$
--
--   **Role.** This is the per-period form of Lemma 4.8: when the selected auxiliary action is uniform among $M$ candidates, the learner plays it in at most $r/M$ rounds, as if guessing, plus a term that is small because one observation carries only $\eta^2/3$ nats about the selection (Lemma 4.7).
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (STOC 2027 submission 1457), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1457.pdf, proof of Lemma 4.8, pp. 17–19 (one period, worlds $j$ and $0$). Statement taken from jasonhartline's accepted Lean proof of CalibeatBandit.theorem_4_1 (submission 0ae8d87e-4337-4d82-8722-8eeded8a7691).

import Definitions.Def_CalibeatBandit_hard_tree_analysis

set_option autoImplicit false

open CalibeatBandit Filter MeasureTheory Set InformationTheory ProbabilityTheory
open scoped Interval ENNReal BigOperators

theorem CalibeatBandit.integral_periodHits_average_le {h M U N : ℕ}
    (e : Fin N ≃ TreeAction h M U) (η : ℝ) (hη : 0 ≤ η) (hη₁ : η < 1)
    (leaf : Fin (2 ^ h)) (coin : TreeNode h → Bool) (leafCoin : ℕ → Bool) (dummy : Fin M)
    (pick : (t : ℕ) → FeedbackHistory t → Fin N) (hm : ∀ t, Measurable (pick t)) (r : ℕ) :
    let u (j : Fin M) (t : ℕ) (i : Fin N) := treeBonusProb leaf coin (leafCoin t) j (e i)
    (∑ j : Fin M, ∫ tape, periodHits η (u j) pick (e.symm (.inr (.inl j))) r tape ∂rewardTapeLaw N r) / M
      ≤ (r : ℝ) / M + η * r * Real.sqrt ((r : ℝ) / (6 * M)) := by sorry
