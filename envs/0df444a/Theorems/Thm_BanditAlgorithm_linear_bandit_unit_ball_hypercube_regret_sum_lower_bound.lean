-- Prove2me | Theorems.Thm_BanditAlgorithm_linear_bandit_unit_ball_hypercube_regret_sum_lower_bound
-- name    : BanditAlgorithm.linear_bandit_unit_ball_hypercube_regret_sum_lower_bound
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-29T18:01:40.327419+00:00
-- url     : https://prove2.me/theorems/88a55e88-2a70-496a-8fe4-72d210ea8483
-- title:
--   Unit-ball linear bandit hypercube regret-sum lower bound
-- statement:
--   Let $d,n$ be positive integers with $d\le 2n$, let
--
--   $$
--   \mathcal A=\{a\in\mathbb R^d:\|a\|_2\le 1\},
--   $$
--
--   and let $\pi$ be any stochastic linear-bandit policy supported on $\mathcal A$. Put
--
--   $$
--   \Delta=\sqrt{\frac{d}{48n}}.
--   $$
--
--   For each sign vector $\sigma\in\{-1,1\}^d$, let $\theta_\sigma=\Delta\sigma$, and denote by $R_n(\mathcal A,\theta_\sigma;\pi)$ the expected regret of $\pi$ after $n$ rounds in the unit-variance Gaussian linear bandit with parameter $\theta_\sigma$. Then the sum of the regrets over the whole parameter hypercube satisfies
--
--   $$
--   \sum_{\sigma\in\{-1,1\}^d}R_n(\mathcal A,\theta_\sigma;\pi)
--   \;\ge\;
--   2^d\,\frac{n\Delta\sqrt d}{4}.
--   $$
--
--   Equivalently, the average regret over the hypercube is at least $n\Delta\sqrt d/4$. This is the quantitative hypercube-averaging core of the unit-ball minimax lower bound and is reusable independently of the final finite-averaging and constant calculation.
--
--   **Formalization Note** Sign vectors are indexed by Boolean-valued functions on `Fin d`; `false` represents $-1$ and `true` represents $1$. The factor $2^d$ is written as the cardinality of that finite Boolean function space.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (Cambridge University Press, 2020), Theorem 24.2, pp. 290–291, especially Eqs. (24.3)–(24.5) and the concluding randomisation-hammer display; https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_LinearBanditProtocol

open Matrix MeasureTheory

theorem BanditAlgorithm.linear_bandit_unit_ball_hypercube_regret_sum_lower_bound
    {d n : ℕ} (hd : 0 < d) (hdn : d ≤ 2 * n)
    (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy
      {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1} π) :
    let Δ := Real.sqrt ((d : ℝ) / (48 * n))
    (Fintype.card (Fin d → Bool) : ℝ) *
          (n * Δ * Real.sqrt d / 4) ≤
      ∑ σ : Fin d → Bool,
        linearBanditExpectedRegret
          {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1}
          (fun i ↦ Δ * if σ i then 1 else -1) π n := by
  sorry
