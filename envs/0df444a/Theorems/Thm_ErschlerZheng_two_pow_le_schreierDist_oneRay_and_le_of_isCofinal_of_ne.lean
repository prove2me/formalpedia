-- Prove2me | Theorems.Thm_ErschlerZheng_two_pow_le_schreierDist_oneRay_and_le_of_isCofinal_of_ne
-- name    : ErschlerZheng.two_pow_le_schreierDist_oneRay_and_le_of_isCofinal_of_ne
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T01:18:17.443887+00:00
-- url     : https://prove2.me/theorems/e8ad733d-32d7-43e8-8630-8b31598d5684
-- title:
--   Fact 7.3 — for x ≠ 1^∞ cofinal with 1^∞, 2^{n(x)−1} ⩽ d_𝒮(x, 1^∞) ⩽ 2^{n(x)} − 1, where n(x) is the position of the last 0 of x
-- statement:
--   For every string $\omega \in \{\mathbf 0, \mathbf 1, \mathbf 2\}^{\mathbb N}$ and every ray $x$ cofinal with $1^\infty$ (`IsCofinal`) with $x \neq 1^\infty$,
--   $$2^{n(x) - 1} \le d_{\mathcal S_\omega}(x, 1^\infty) \le 2^{n(x)} - 1,$$
--   where $n(x) = \max\{k : x_k = 0\}$ (`maxZeroIndex`, digits numbered from 1) and $d_{\mathcal S_\omega}$ is the Schreier distance (`schreierDist`).
--
--   Erschler and Zheng, p. 35, Fact 7.3: “Let $x \in \partial \mathsf T$ be a point that is cofinal with $1^\infty$. Let $n(x) = \max\{k : x_k = 0\}$. Then $2^{n(x)-1} \leqslant d_{\mathcal S}(x, 1^\infty) \leqslant 2^{n(x)} - 1$.”
--
--   The hypothesis $x \neq 1^\infty$ is not printed; for $x = 1^\infty$ the maximum defining $n(x)$ is over the empty set, so the printed bounds are undefined there. The distance does not depend on $\omega$ ([`ErschlerZheng.orbitOne_eq_and_adjacent_iff_and_card_eq_and_schreierDist_eq`](https://prove2.me/theorems/407877ac-caa9-4735-bc30-3d651039d391)), and the statement is made for every $\omega$.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 35, Fact 7.3

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk

namespace ErschlerZheng

theorem two_pow_le_schreierDist_oneRay_and_le_of_isCofinal_of_ne (ω : ℕ → Fin 3) (x : Ray)
    (hx : IsCofinal x) (hxo : x ≠ oneRay) :
    2 ^ (maxZeroIndex x - 1) ≤ schreierDist ω x oneRay ∧
      schreierDist ω x oneRay ≤ 2 ^ maxZeroIndex x - 1 := by
  sorry

end ErschlerZheng
