-- Prove2me | Theorems.Thm_CalibeatBandit_lemma_4_7
-- name    : CalibeatBandit.lemma_4_7
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-23T18:36:12.487943+00:00
-- url     : https://prove2.me/theorems/f5426ee5-b642-4723-87cb-5a0204fe7ed5
-- title:
--   Lemma 4.7 — $\mathrm{KL}(Q_0\,\|\,Q_1)\le\eta^2/3$ for $Z\sim U[0,1]$ and $h_\eta(Z)=Z+\eta Z(1-Z)$
-- statement:
--   **Lemma 4.7.** Let $0\le\eta<1$, let $Z$ be uniform on $[0,1]$ with law $Q_0$, and let $Q_1$ be the law of $h_\eta(Z)$, where $h_\eta(z)=z+\eta z(1-z)$. Then
--
--   $$\mathrm{KL}(Q_0\,\|\,Q_1)\ \le\ \frac{\eta^2}{3}.$$
--
--   **Role.** In the lower-bound construction a reward without bonus is $\frac18+\frac18Z$ and a reward with bonus is $\frac18+\frac18Z+\frac\eta8Z(1-Z)$; after the affine change $\hat y=8y-1$ these are $Z$ and $h_\eta(Z)$. The lemma says that one observation of an action carries at most $\eta^2/3$ nats of information about whether that action has the bonus, although the bonus changes the mean reward by an amount of order $\eta$. This gap between information and reward is what makes the selected auxiliary action impossible to find within one period.
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (STOC 2027 submission 1457), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1457.pdf, Lemma 4.7, p. 17 (proof in Appendix D). Statement taken from jasonhartline's accepted Lean proof of CalibeatBandit.theorem_4_1 (submission 0ae8d87e-4337-4d82-8722-8eeded8a7691).

import Definitions.Def_CalibeatBandit_hard_tree_analysis

set_option autoImplicit false

open CalibeatBandit Filter MeasureTheory Set InformationTheory ProbabilityTheory
open scoped Interval ENNReal BigOperators

theorem CalibeatBandit.lemma_4_7 {η : ℝ} (hη₀ : 0 ≤ η) (hη₁ : η < 1) :
    let Q := volume.restrict (Icc (0 : ℝ) 1)
    klDiv Q (Q.map (bonusTransform η)) ≤ ENNReal.ofReal (η ^ 2 / 3) := by sorry
