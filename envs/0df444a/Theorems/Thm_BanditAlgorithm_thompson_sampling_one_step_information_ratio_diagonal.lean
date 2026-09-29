-- Prove2me | Theorems.Thm_BanditAlgorithm_thompson_sampling_one_step_information_ratio_diagonal
-- name    : BanditAlgorithm.thompson_sampling_one_step_information_ratio_diagonal
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-01T23:37:42.295373+00:00
-- url     : https://prove2.me/theorems/30a9e899-2d4c-4cc8-bdba-dd93e1ac29cf
-- title:
--   One-step Thompson-sampling diagonal information-ratio bound
-- statement:
--   Fix a posterior weight vector $p$ on $k$ actions. For each action $a$, let $P_a$ be the conditional observation law on the event that $a$ is optimal, let $M$ be the posterior-predictive observation law, and let $r_a\in[0,1]$ be the reward observable. If every $D(P_a\,\|\,M)$ is finite, then
--
--   $$
--   \left[\sum_a p_a\left(\mathbb E_{P_a}r_a-\mathbb E_M r_a\right)\right]^2\le \frac{k}{2}\sum_a p_a^2D(P_a\,\|\,M).
--   $$
--
--   The right side is the diagonal contribution to the information gained by posterior sampling.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (Cambridge UP, 2020), https://tor-lattimore.com/downloads/book/book.pdf, printed p. 470 (PDF p. 479), Lemma 36.7 and its proof: Pinsker followed by Cauchy–Schwarz, before the final Bayes-rule identification.

import Mathlib.InformationTheory.KullbackLeibler.Basic

open MeasureTheory InformationTheory
open scoped ENNReal BigOperators

theorem BanditAlgorithm.thompson_sampling_one_step_information_ratio_diagonal
    {k : ℕ} {Omega : Type} {mOmega : MeasurableSpace Omega}
    (p : Fin k → ℝ) (P : Fin k → Measure Omega)
    [∀ a, IsProbabilityMeasure (P a)]
    (M : Measure Omega) [IsProbabilityMeasure M]
    (reward : Fin k → Omega → ℝ)
    (hreward : ∀ a, Measurable (reward a))
    (hreward0 : ∀ a x, 0 ≤ reward a x)
    (hreward1 : ∀ a x, reward a x ≤ 1)
    (hfinite : ∀ a, klDiv (P a) M ≠ ∞) :
    (∑ a, p a * ((∫ x, reward a x ∂(P a)) - ∫ x, reward a x ∂M)) ^ 2 ≤
      ((k : ℝ) / 2) * ∑ a, p a ^ 2 * (klDiv (P a) M).toReal := by
  sorry
