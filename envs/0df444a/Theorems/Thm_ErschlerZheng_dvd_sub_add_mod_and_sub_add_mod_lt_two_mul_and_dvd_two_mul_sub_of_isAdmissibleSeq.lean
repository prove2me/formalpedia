-- Prove2me | Theorems.Thm_ErschlerZheng_dvd_sub_add_mod_and_sub_add_mod_lt_two_mul_and_dvd_two_mul_sub_of_isAdmissibleSeq
-- name    : ErschlerZheng.dvd_sub_add_mod_and_sub_add_mod_lt_two_mul_and_dvd_two_mul_sub_of_isAdmissibleSeq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T11:16:24.390981+00:00
-- url     : https://prove2.me/theorems/53ba880d-78e2-4382-a2b6-17c770721bb6
-- title:
--   Supporting fact for |𝔉_{j,n}| (p. 40), not in the paper — D | n − j + j̄ < 2k_n and D | 2k_n − (n − j + j̄), so the exponent (2k_n − (n − j + j̄))/D is exact in ℕ
-- statement:
--   Let $(k_n)$ satisfy the standing assumption of p. 40 (`IsAdmissibleSeq D k`), let $n \ge 1$ be divisible by $D$, and let $j \le n$ with $n < j + k_n$. Write $\bar j = j \bmod D$ (`j % D`) and take subtractions in $\mathbb N$. Then $D$ divides $n - j + \bar j$, $n - j + \bar j < 2k_n$, and $D$ divides $2k_n - (n - j + \bar j)$.
--
--   This is not a result of the paper. It backs the sentence of the note of `injOn_gTilde_and_ncard_fSet_eq` on the exponent in $|\mathfrak F_{j,n}| = 2^{(2k_n - (n-j+\bar j))/D}$: “The exponent is computed in $\mathbb N$, and exactly: $n - j + \bar j$ is a multiple of $D$ because $D$ divides $n$, and it is less than $2k_n$ because $n - j < k_n$ and $\bar j < D \le k_n$.” The hypotheses of `ErschlerZheng.injOn_gTilde_and_ncard_fSet_eq` include $1 \le j \le n$, $D \mid n$ and $n < j + k_n$, so they give those used here.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 40, the exponent of |𝔉_{j,n}| is an integer (supporting fact, not in the paper)

import Mathlib
import Definitions.Def_ErschlerZheng_Construction

namespace ErschlerZheng

theorem dvd_sub_add_mod_and_sub_add_mod_lt_two_mul_and_dvd_two_mul_sub_of_isAdmissibleSeq (D : ℕ)
    (k : ℕ → ℕ) (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n) (hn1 : 1 ≤ n) (j : ℕ)
    (hjn : n < j + k n) (hjn' : j ≤ n) :
    D ∣ n - j + j % D ∧ n - j + j % D < 2 * k n ∧ D ∣ 2 * k n - (n - j + j % D) := by
  sorry

end ErschlerZheng
