-- Prove2me | Theorems.Thm_ErschlerZheng_isProbability_and_hasFiniteEntropy_muBeta_and_mass_ball_compl_le
-- name    : ErschlerZheng.isProbability_and_hasFiniteEntropy_muBeta_and_mass_ball_compl_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T09:44:19.210414+00:00
-- url     : https://prove2.me/theorems/ba0d82f0-aeaf-4d43-adc6-9aa2c7ce0c93
-- title:
--   Corollary 8.2 — for β > 0 and k_n ⩽ n, μ_β is a probability of finite entropy with μ_β(B(id, 2^{2k_n}L^ω_n)^c) ⩽ C/2^{nβ}, C depending on β and D
-- statement:
--   Let $\beta > 0$. Then there is $C > 0$ such that for every string $\omega$ satisfying Assumption $(\mathrm{Fr}(D))$ (`SatisfiesFr`) and every sequence $(k_n)$ satisfying the standing assumption of p. 40 (`IsAdmissibleSeq`) with $k_n \le n$ for all large $n$, the measure $\mu_\beta$ of (7.11) (`muBeta`) is a probability (`IsProbability`) of finite entropy (`HasFiniteEntropy`), and for every $n$
--   $$\mu_\beta\bigl(B(id, 2^{2k_n}L^\omega_n)^c\bigr) \le \frac{C}{2^{n\beta}},$$
--   where $B(id, R)$ is the ball of radius $R$ for the generating set $\{a, b_\omega, c_\omega, d_\omega\}$ (`ball (genSet ω)`) and $L^\omega_n$ is the number (8.1) (`lengthL`).
--
--   Erschler and Zheng, p. 57, Corollary 8.2: “Let $\mu_\beta$ be defined as in (7.11) with parameters $\beta > 0$ and $(k_n)$, $k_n \leqslant n$. Then $\mu_\beta$ is of finite entropy and there exists constant $C > 0$ depending on $\beta, D$ such that $\mu_\beta(B(id, 2^{2k_n}L^\omega_n)^c) \leqslant \frac{C}{2^{n\beta}}$.”
--
--   “$k_n \leqslant n$” is read as holding for all large $n$, not for every $n$: the choice $k_n = A\lfloor\log_2 n\rfloor$ of Theorem 8.3 has $k_2 = A$ ([`ErschlerZheng.isAdmissibleSeq_kLog_and_kLog_two_eq_and_kLog_three_eq`](https://prove2.me/theorems/011081e3-0764-4abc-aca5-5b8139e58296)), which exceeds $2$ once $A > 2$. The proof uses the hypothesis only to bound $\sum_{D|n}2^{-n\beta}(n + 2k_n^2)$, where finitely many terms do not matter. This weakens a printed hypothesis. The constant is chosen before $\omega$ and $(k_n)$, depending only on $\beta$ and $D$ as printed. The first conclusion, that $\mu_\beta$ is a probability, is the normalization (7.11) asserts (“$C_\beta > 0$ is the normalization constant such that $\mu_\beta$ is a probability measure”, p. 41). The standing assumptions are those of §7.2 (pp. 35 and 40).
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 57, Corollary 8.2

import Mathlib
import Definitions.Def_ErschlerZheng_Construction

namespace ErschlerZheng

theorem isProbability_and_hasFiniteEntropy_muBeta_and_mass_ball_compl_le (D : ℕ) (β : ℝ)
    (hβ : 0 < β) :
    ∃ C > (0 : ℝ), ∀ ω : ℕ → Fin 3, SatisfiesFr D ω → ∀ k : ℕ → ℕ, IsAdmissibleSeq D k →
      (∀ᶠ n in Filter.atTop, k n ≤ n) →
        IsProbability (muBeta D ω k β) ∧ HasFiniteEntropy (muBeta D ω k β) ∧
          ∀ n : ℕ, mass (muBeta D ω k β) (ball (genSet ω) (2 ^ (2 * k n) * lengthL ω n))ᶜ ≤
            C / (2 : ℝ) ^ ((n : ℝ) * β) := by
  sorry

end ErschlerZheng
