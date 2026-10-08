-- Prove2me | Theorems.Thm_ErschlerZheng_existsUnique_pos_root_and_alpha0_approx_and_charpoly_matrixM
-- name    : ErschlerZheng.existsUnique_pos_root_and_alpha0_approx_and_charpoly_matrixM
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T02:32:47.274971+00:00
-- url     : https://prove2.me/theorems/fdf7cb37-4cf2-43d0-b0d2-f089f2d15823
-- title:
--   pp. 2, 29, 59 — X³ − X² − 2X − 4 has a unique positive root λ_0, the spectral radius of M; α_0 = log 2/log λ_0 ≈ 0.7674 and λ_0 = 2/η_0
-- statement:
--   1. The polynomial $X^3 - X^2 - 2X - 4$ has exactly one positive real root;
--   2. $\lambda_0$ (`lambda0`) is positive and is a root of it;
--   3. $\alpha_0 = \log 2/\log \lambda_0$ (`alpha0`) satisfies $|\alpha_0 - 0.7674| < 5 \cdot 10^{-5}$;
--   4. the characteristic polynomial over $\mathbb Z$ of the matrix $M$ of p. 28 (`matrixM`, rows $(1, 2, 0)$, $(1, 0, 2)$, $(1, 0, 0)$) is $X^3 - X^2 - 2X - 4$;
--   5. every complex root $z$ of $X^3 - X^2 - 2X - 4$ has $|z| \le \lambda_0$;
--   6. $\lambda_0$ is the spectral radius of $M$: it lies in the spectrum of $M$ as a complex matrix, and every $z$ in that spectrum has $|z| \le \lambda_0$;
--   7. the polynomial $X^3 + X^2 + X - 2$ has exactly one real root $\eta_0$, and $\lambda_0 = 2/\eta_0$.
--
--   Erschler and Zheng, p. 2: “where $\alpha_0 = \frac{\log 2}{\log \lambda_0} \approx 0.7674$, where $\lambda_0$ is the positive root of the polynomial $X^3 - X^2 - 2X - 4$.” p. 29: “where $\lambda_0$ is the spectral radius of $M$, that is the positive root of the characteristic polynomial $X^3 - X^2 - 2X - 4$.” and p. 59, Theorem 8.5: “where $\eta_0$ is the real root of $X^3 + X^2 + X - 2$.”
--
--   The phrases “the positive root” and “the real root” presuppose uniqueness (conjuncts 1 and 7); “$\approx 0.7674$” is read as agreement to four decimal places (conjunct 3); “the spectral radius of $M$” is conjunct 6, and “that is the positive root of the characteristic polynomial” is conjuncts 1, 2 and 4. The relation $\lambda_0 = 2/\eta_0$ is not printed; it connects the $\eta_0$ of Theorem 8.5, which p. 59 calls the “sum contracting coefficient” of the string $\mathbf{201}$ “(as in the first Grigorchuk group)”, to $\lambda_0$, and follows by substituting $X = 2/x$.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 2, the constants λ_0 and α_0, with pp. 29, 33 and 59

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk

namespace ErschlerZheng

theorem existsUnique_pos_root_and_alpha0_approx_and_charpoly_matrixM :
    (∃! x : ℝ, 0 < x ∧ x ^ 3 - x ^ 2 - 2 * x - 4 = 0) ∧
      (0 < lambda0 ∧ lambda0 ^ 3 - lambda0 ^ 2 - 2 * lambda0 - 4 = 0) ∧
      |alpha0 - 7674 / 10000| < 5 / 100000 ∧
      (matrixM.map (Nat.cast : ℕ → ℤ)).charpoly =
        Polynomial.X ^ 3 - Polynomial.X ^ 2 - 2 * Polynomial.X - 4 ∧
      (∀ z : ℂ, z ^ 3 - z ^ 2 - 2 * z - 4 = 0 → ‖z‖ ≤ lambda0) ∧
      ((lambda0 : ℂ) ∈ spectrum ℂ (matrixM.map (Nat.cast : ℕ → ℂ)) ∧
        ∀ z ∈ spectrum ℂ (matrixM.map (Nat.cast : ℕ → ℂ)), ‖z‖ ≤ lambda0) ∧
      ∃ η : ℝ, η ^ 3 + η ^ 2 + η - 2 = 0 ∧ (∀ y : ℝ, y ^ 3 + y ^ 2 + y - 2 = 0 → y = η) ∧
        lambda0 = 2 / η := by
  sorry

end ErschlerZheng
