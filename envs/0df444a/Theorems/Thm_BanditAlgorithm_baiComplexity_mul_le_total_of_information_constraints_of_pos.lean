-- Prove2me | Theorems.Thm_BanditAlgorithm_baiComplexity_mul_le_total_of_information_constraints_of_pos
-- name    : BanditAlgorithm.baiComplexity_mul_le_total_of_information_constraints_of_pos
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-30T19:00:29.112759+00:00
-- url     : https://prove2.me/theorems/46d0fb52-1c4e-40f9-be88-2f46e79b30d0
-- title:
--   Best-arm complexity optimization bridge
-- statement:
--   Fix a bandit environment $\nu$ with $k\ge1$ arms in a class $\mathcal E$. Let $c_i\in[0,\infty]$ be nonnegative sampling weights and let $L\in[0,\infty]$. Suppose every alternative environment $\nu'\in\mathcal E_{\mathrm{alt}}(\nu)$ satisfies the information constraint
--
--   $$
--   L\le \sum_{i=1}^k c_i D(\nu_i\Vert\nu_i').
--   $$
--
--   Then the characteristic best-arm-identification time obeys
--
--   $$
--   c^*(\nu)\,L\le \sum_{i=1}^k c_i.
--   $$
--
--   This is the optimization step that converts per-alternative change-of-measure inequalities into the closed-form sample-complexity lower bound.
--
--   **Formalization Note** All quantities are extended nonnegative reals, including zero and infinite boundary cases.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), proof of Theorem 33.5, printed p. 407, Eq. (33.7).

import Definitions.Def_BanditTrajectory

open MeasureTheory ProbabilityTheory InformationTheory ENNReal

theorem BanditAlgorithm.baiComplexity_mul_le_total_of_information_constraints_of_pos
    {k : ℕ} (hk : 0 < k) (𝓔 : Set (StochasticBandit k)) (ν : StochasticBandit k)
    (c : Fin k → ℝ≥0∞) (L : ℝ≥0∞)
    (hinfo : ∀ ν' ∈ baiAlternatives 𝓔 ν,
      L ≤ ∑ i, c i * klDiv (ν.P i) (ν'.P i)) :
    baiComplexity ν 𝓔 * L ≤ ∑ i, c i := by
  sorry
