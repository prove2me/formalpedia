-- Prove2me | Theorems.Thm_ErschlerZheng_mul_ellIndex_eq_iff_dvd
-- name    : ErschlerZheng.mul_ellIndex_eq_iff_dvd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T11:16:12.912652+00:00
-- url     : https://prove2.me/theorems/57d26fc3-0003-4973-8f30-ed1f400cba02
-- title:
--   Supporting fact for ℓ(k, j) in (7.3), not in the paper — the natural-number division in ℓ(k, j) = (j + D − j̄ + k)/D is exact exactly when D | k
-- statement:
--   For all natural numbers $D$, $k$ and $j$, with $\bar j = j \bmod D$ (`j % D`), the natural-number quotient $\ell(k, j) = \lfloor (j + D - \bar j + k)/D \rfloor$ (`ellIndex D k j`, with subtraction and division in $\mathbb N$) satisfies
--
--   $$D \cdot \ell(k, j) = j + D - \bar j + k$$
--
--   if and only if $D$ divides $k$.
--
--   This is not a result of the paper, which defines $\ell(k, j) = \frac1D(j + D - \bar j + k)$ in (7.3) for $k$ divisible by $D$ (p. 37: “Let $k$ be an integer divisible by $D$, write $\ell(k, j) = \frac1D(j + D - \bar j + k)$”). It backs the sentence of the Construction bundle note `ErschlerZheng_Construction`: “`ellIndex` divides in $\mathbb N$, which is exact when $D$ divides $k$, since $j + D - \bar j$ is a multiple of $D$”.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 37, ℓ(k, j) is an integer exactly when D divides k (supporting fact, not in the paper)

import Mathlib
import Definitions.Def_ErschlerZheng_Construction

namespace ErschlerZheng

theorem mul_ellIndex_eq_iff_dvd (D k j : ℕ) :
    D * ellIndex D k j = j + D - j % D + k ↔ D ∣ k := by
  sorry

end ErschlerZheng
