-- Prove2me | Theorems.Thm_ErschlerZheng_exists_measure_mass_compl_ball_le_rpow_and_exp_le_growth_of_satisfiesFr
-- name    : ErschlerZheng.exists_measure_mass_compl_ball_le_rpow_and_exp_le_growth_of_satisfiesFr
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T10:05:22.111262+00:00
-- url     : https://prove2.me/theorems/497562df-4353-45c7-ab50-79c9c1c648c7
-- title:
--   Theorem 8.3, as printed — under Fr(D), for ε > 0 a non-degenerate symmetric finite-entropy μ on G_ω with non-trivial boundary, μ(B(id, L^ω_n)^c) ⩽ Cn^{−1+ε} and v(L^ω_n) ⩾ exp(cn^{1−ε})
-- statement:
--   Let $\epsilon > 0$. Then there is $C > 0$ such that for every string $\omega$ satisfying Assumption $(\mathrm{Fr}(D))$ (`SatisfiesFr`) there is a function $\mu$ on $G_\omega$ (`grigorchuk ω`) that is a non-degenerate (`IsNondegenerate`), symmetric (`IsSymmetric`) probability (`IsProbability`) of finite entropy (`HasFiniteEntropy`) with non-trivial Poisson boundary (`HasNontrivialPoissonBoundary`), such that
--   $$\mu\bigl(B(id, L^\omega_n)^c\bigr) \le C\,n^{-1+\epsilon} \quad \text{for every } n \ge 1,$$
--   and there is $c > 0$ with
--   $$v_{G_\omega,S}(L^\omega_n) \ge \exp\bigl(c\,n^{1-\epsilon}\bigr) \quad \text{for every } n \ge 1.$$
--   Here $S = \{a, b_\omega, c_\omega, d_\omega\}$ (`genSet ω`), $B(id, R)$ is the ball of radius $R$ (`ball`), $v_{G_\omega,S}$ is the growth function (`growth`), $L^\omega_n$ is the number (8.1) (`lengthL`), and the powers of $n$ are real powers (`Real.rpow`).
--
--   Erschler and Zheng, p. 58, Theorem 8.3: “Let $\omega$ be a string satisfying Assumption $(\mathrm{Fr}(D))$. For any $\epsilon > 0$, there exists a constant $C = C(D, \epsilon) > 0$ and a non-degenerate symmetric probability measure $\mu$ on $G_\omega$ of finite entropy and nontrivial Poisson boundary with tail decay $\mu(B(id, L^\omega_n)^c) \leqslant Cn^{-1+\epsilon}$, where the number $L^\omega_n$ is defined in (8.1). As a consequence, there exists constant $c = c(\omega, \epsilon) > 0$ such that for all $n \geqslant 1$, $v_{G_\omega,S}(L^\omega_n) \geqslant \exp(cn^{1-\epsilon})$.”
--
--   This is Theorem 8.3 as printed. The milestone [`ErschlerZheng.exists_measure_mass_compl_ball_le_and_exp_le_growth_of_satisfiesFr`](https://prove2.me/theorems/1a116650-da25-4d01-b0a9-a02693d2c364) asserts the version with $2^n$ in place of $n$, and this statement follows from it: for $\epsilon \le 1$ from that version at the same $\epsilon$, and for $\epsilon > 1$ from it at $\epsilon = \tfrac12$ (the route below). As there, $C$ is chosen before $\omega$, as $C = C(D, \epsilon)$ says, and $c$ after $\omega$ and $\mu$, as $c = c(\omega, \epsilon)$ says; both bounds are asserted for $n \ge 1$, the range of the printed consequence.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 58, Theorem 8.3 as printed

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk

namespace ErschlerZheng

theorem exists_measure_mass_compl_ball_le_rpow_and_exp_le_growth_of_satisfiesFr (D : ℕ) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ ω : ℕ → Fin 3, SatisfiesFr D ω →
      ∃ μ : grigorchuk ω → ℝ, IsNondegenerate μ ∧ IsSymmetric μ ∧ IsProbability μ ∧
        HasFiniteEntropy μ ∧ HasNontrivialPoissonBoundary μ ∧
        (∀ n : ℕ, 1 ≤ n →
          mass μ (ball (genSet ω) (lengthL ω n))ᶜ ≤ C * (n : ℝ) ^ (-1 + ε)) ∧
        ∃ c > (0 : ℝ), ∀ n : ℕ, 1 ≤ n →
          Real.exp (c * (n : ℝ) ^ (1 - ε)) ≤ growth (genSet ω) (lengthL ω n) := by
  sorry

end ErschlerZheng
