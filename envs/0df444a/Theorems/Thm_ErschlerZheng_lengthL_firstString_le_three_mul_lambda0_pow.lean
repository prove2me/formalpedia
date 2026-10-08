-- Prove2me | Theorems.Thm_ErschlerZheng_lengthL_firstString_le_three_mul_lambda0_pow
-- name    : ErschlerZheng.lengthL_firstString_le_three_mul_lambda0_pow
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T10:19:51.216982+00:00
-- url     : https://prove2.me/theorems/185145e4-f437-4b96-87e3-6ed58a7b04ec
-- title:
--   p. 59 — for ω = (012)^∞, L^ω_n ⩽ 3λ_0^n for every n
-- statement:
--   For $\omega = (\mathbf{012})^\infty$ (`firstString`) and every $n \in \mathbb N$,
--   $$L^\omega_n \le 3\lambda_0^n,$$
--   where $L^\omega_n = (1\ 1\ 1)\, M_{\omega_0} \cdots M_{\omega_{n-1}}\, (1\ 1\ 1)^T$ (`lengthL`) and $\lambda_0$ (`lambda0`) is the positive root of $X^3 - X^2 - 2X - 4$.
--
--   Erschler and Zheng, p. 59, proof of Theorem A: “Explicit calculation of eigenvalues the substitution matrix shows that $L_n = L_n^{(\mathbf{012})} \leqslant 3\lambda_0^n$, where $\lambda_0$ is the positive root of the polynomial $X^3 - X^2 - 2X - 4$.”
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 59, L^{(012)}_n ⩽ 3λ_0^n

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk

namespace ErschlerZheng

theorem lengthL_firstString_le_three_mul_lambda0_pow (n : ℕ) :
    (lengthL firstString n : ℝ) ≤ 3 * lambda0 ^ n := by
  sorry

end ErschlerZheng
