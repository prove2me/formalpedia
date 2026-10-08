-- Prove2me | Theorems.Thm_ErschlerZheng_exists_measure_mass_compl_ball_le_and_exp_le_growth_of_satisfiesFr
-- name    : ErschlerZheng.exists_measure_mass_compl_ball_le_and_exp_le_growth_of_satisfiesFr
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T11:27:19.412483+00:00
-- url     : https://prove2.me/theorems/1a116650-da25-4d01-b0a9-a02693d2c364
-- title:
--   Theorem 8.3, with 2^n as proved — under Fr(D), for ε > 0 a non-degenerate symmetric finite-entropy μ on G_ω with non-trivial boundary, μ(B(id, L^ω_n)^c) ⩽ C2^{−(1−ε)n} and v(L^ω_n) ⩾ exp(c2^{(1−ε)n})
-- statement:
--   Let $\epsilon > 0$. Then there is $C > 0$ such that for every string $\omega$ satisfying Assumption $(\mathrm{Fr}(D))$ (`SatisfiesFr`) there is a function $\mu$ on $G_\omega$ (`grigorchuk ω`) that is a non-degenerate (`IsNondegenerate`), symmetric (`IsSymmetric`) probability (`IsProbability`) of finite entropy (`HasFiniteEntropy`) with non-trivial Poisson boundary (`HasNontrivialPoissonBoundary`), such that
--   $$\mu\bigl(B(id, L^\omega_n)^c\bigr) \le C\,2^{-(1-\epsilon)n} \quad \text{for every } n \ge 1,$$
--   and there is $c > 0$ with
--   $$v_{G_\omega,S}(L^\omega_n) \ge \exp\bigl(c\,2^{(1-\epsilon)n}\bigr) \quad \text{for every } n \ge 1.$$
--   Here $S = \{a, b_\omega, c_\omega, d_\omega\}$ (`genSet ω`), $B(id, R)$ is the ball of radius $R$ (`ball`), $v_{G_\omega,S}$ is the growth function (`growth`), and $L^\omega_n$ is the number (8.1) (`lengthL`).
--
--   Erschler and Zheng, p. 58, Theorem 8.3: “Let $\omega$ be a string satisfying Assumption $(\mathrm{Fr}(D))$. For any $\epsilon > 0$, there exists a constant $C = C(D, \epsilon) > 0$ and a non-degenerate symmetric probability measure $\mu$ on $G_\omega$ of finite entropy and nontrivial Poisson boundary with tail decay $\mu(B(id, L^\omega_n)^c) \leqslant Cn^{-1+\epsilon}$, where the number $L^\omega_n$ is defined in (8.1). As a consequence, there exists constant $c = c(\omega, \epsilon) > 0$ such that for all $n \geqslant 1$, $v_{G_\omega,S}(L^\omega_n) \geqslant \exp(cn^{1-\epsilon})$.”
--
--   The proof gives $2^n$ where the statement prints $n$. The proof gives $\mu_\beta(B(id, n^{2A}L^\omega_n)^c) \le C/2^{n\beta}$ with $\beta > 1 - \epsilon$ (p. 58; the milestone `ErschlerZheng.isProbability_and_hasFiniteEntropy_muBeta_and_mass_ball_compl_le`, at the radius $2^{2k_n}L^\omega_n$), and since $L^\omega_{n+1} \ge 2L^\omega_n$ (`ErschlerZheng.two_mul_lengthL_le_lengthL_succ`) that is the tail bound $C\,2^{-(1-\epsilon)n}$ at the radius $L^\omega_n$; Lemma 2.1 (`ErschlerZheng.exp_le_growth_of_hasNontrivialPoissonBoundary`) then gives $\exp(c\,2^{(1-\epsilon)n})$. The statement asserts that form; the printed bounds, weaker for $\epsilon \le 1$, are stated as printed in `ErschlerZheng.exists_measure_mass_compl_ball_le_rpow_and_exp_le_growth_of_satisfiesFr`.
--
--   Theorem A needs the stronger form. The paper obtains it as “the special case of Theorem 8.3 applied to the periodic sequence $(\mathbf{012})^\infty$” (p. 59), and its exponent $\alpha_0 = \log 2/\log\lambda_0$ comes from comparing $2^n$ with $L^\omega_n \le 3\lambda_0^n$ for $\omega = (\mathbf{012})^\infty$ (`ErschlerZheng.lengthL_firstString_le_three_mul_lambda0_pow`). The printed bounds are powers of $n$, and $L^\omega_n \ge 3 \cdot 2^n$ (`ErschlerZheng.two_mul_lengthL_le_lengthL_succ`), so they are powers of $\log L^\omega_n$ and give no exponent.
--
--   $C$ is chosen before $\omega$, as $C = C(D, \epsilon)$ says, and $c$ after $\omega$ and $\mu$, as $c = c(\omega, \epsilon)$ says. The tail bound is asserted for $n \ge 1$, the range of the printed consequence. A measure on $G_\omega$ is a function $G_\omega \to \mathbb R$ (Walks bundle note).
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 58, Theorem 8.3, with n replaced by 2^n

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk

namespace ErschlerZheng

theorem exists_measure_mass_compl_ball_le_and_exp_le_growth_of_satisfiesFr (D : ℕ) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ ω : ℕ → Fin 3, SatisfiesFr D ω →
      ∃ μ : grigorchuk ω → ℝ, IsNondegenerate μ ∧ IsSymmetric μ ∧ IsProbability μ ∧
        HasFiniteEntropy μ ∧ HasNontrivialPoissonBoundary μ ∧
        (∀ n : ℕ, 1 ≤ n →
          mass μ (ball (genSet ω) (lengthL ω n))ᶜ ≤ C * (2 : ℝ) ^ (-((1 - ε) * n))) ∧
        ∃ c > (0 : ℝ), ∀ n : ℕ, 1 ≤ n →
          Real.exp (c * (2 : ℝ) ^ ((1 - ε) * n)) ≤ growth (genSet ω) (lengthL ω n) := by
  sorry

end ErschlerZheng
