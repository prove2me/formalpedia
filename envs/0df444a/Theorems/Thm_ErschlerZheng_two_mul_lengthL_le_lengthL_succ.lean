-- Prove2me | Theorems.Thm_ErschlerZheng_two_mul_lengthL_le_lengthL_succ
-- name    : ErschlerZheng.two_mul_lengthL_le_lengthL_succ
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T02:22:21.577331+00:00
-- url     : https://prove2.me/theorems/6f037318-260e-4928-9e52-ac0cf163cbce
-- title:
--   p. 58 — L^ω_{n+1} ⩾ 2L^ω_n for every n and every ω
-- statement:
--   For every string $\omega \in \{\mathbf 0, \mathbf 1, \mathbf 2\}^{\mathbb N}$ and every $n \in \mathbb N$,
--   $$2L^\omega_n \le L^\omega_{n+1},$$
--   where $L^\omega_n = (1\ 1\ 1)\, M_{\omega_0} \cdots M_{\omega_{n-1}}\, (1\ 1\ 1)^T$ (`lengthL`) is the sum of the entries of the product of the matrices $M_i$ of p. 56 (`substMatrix`).
--
--   Erschler and Zheng, p. 58, proof of Theorem 8.3: “Note that $L^\omega_{n+1} \geqslant 2L^\omega_n$ for any $n$ and $\omega$.”
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 58, L^ω_{n+1} ⩾ 2L^ω_n

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk

namespace ErschlerZheng

theorem two_mul_lengthL_le_lengthL_succ (ω : ℕ → Fin 3) (n : ℕ) :
    2 * lengthL ω n ≤ lengthL ω (n + 1) := by
  sorry

end ErschlerZheng
