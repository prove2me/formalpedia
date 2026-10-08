-- Prove2me | Theorems.Thm_ErschlerZheng_schreierDist_eq_abs_sub_grayCode_of_isCofinal
-- name    : ErschlerZheng.schreierDist_eq_abs_sub_grayCode_of_isCofinal
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T01:09:50.024464+00:00
-- url     : https://prove2.me/theorems/095b65fa-2438-4438-bc56-c9f559a82570
-- title:
--   p. 34 — for x, y cofinal with 1^∞, d_𝒮(x, y) = |x̄ − ȳ|, with the Gray code read as suffix sums
-- statement:
--   For every string $\omega \in \{\mathbf 0, \mathbf 1, \mathbf 2\}^{\mathbb N}$ and all rays $x, y$ cofinal with $1^\infty$ (`IsCofinal`),
--   $$d_{\mathcal S_\omega}(x, y) = |\bar x - \bar y|,$$
--   as integers, where $d_{\mathcal S_\omega}$ is the Schreier distance (`schreierDist`) and $\bar x$ (`grayCode`) is the number with binary digits $\bar x_i = \check x_i + \check x_{i+1} + \cdots \bmod 2$, $\check x_i = 1 - x_i$, the digit $\bar x_1$ being the least significant.
--
--   Erschler and Zheng, p. 34: “Explicitly, for $x = x_1x_2 \ldots \in \partial \mathsf T$, flip all digits of $x$ to the ray $\check x_1 \check x_2 \ldots$ where $\check x_i = 1 - x_i$. The Grey code of $x$ is $\bar x = \bar x_1 \bar x_2 \ldots$ where $\bar x_i = \check x_1 + \ldots + \check x_i \mod 2$. Note that for $x$ cofinal with $1^\infty$, its Gray code $\bar x$ has only finitely many 1’s. We regard such an $\bar x$ as an element in $\{0\} \cup \mathbb N$ represented by a binary string. Then on the Schreier graph of $o$, $d_{\mathcal S}(x, y) = |\bar x - \bar y|$.”
--
--   The Gray code is the corrected one of the bundle note, with suffix sums in place of the printed prefix sums ([`ErschlerZheng.isCofinal_and_printed_gray_ones_infinite_prepend_false_oneRay`](https://prove2.me/theorems/b68564c8-cec0-42d7-adc5-213c869096cb)). The paper does not say which digit is the least significant. The statement takes $\bar x_1$, the reading from which Fact 7.3 ([`ErschlerZheng.two_pow_le_schreierDist_oneRay_and_le_of_isCofinal_of_ne`](https://prove2.me/theorems/e8ad733d-32d7-43e8-8630-8b31598d5684)) is proved, as in its proof on p. 35: “the Grey code of $x$ is of the form $u1000\ldots$ where $u$ is a prefix of length $n(x) - 1$”.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 34, the Gray-code distance (suffix sums)

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk

namespace ErschlerZheng

theorem schreierDist_eq_abs_sub_grayCode_of_isCofinal (ω : ℕ → Fin 3) (x y : Ray)
    (hx : IsCofinal x) (hy : IsCofinal y) :
    (schreierDist ω x y : ℤ) = |(grayCode x : ℤ) - grayCode y| := by
  sorry

end ErschlerZheng
