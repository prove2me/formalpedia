-- Prove2me | Theorems.Thm_ErschlerZheng_isCofinal_and_printed_gray_ones_infinite_prepend_false_oneRay
-- name    : ErschlerZheng.isCofinal_and_printed_gray_ones_infinite_prepend_false_oneRay
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T11:15:41.358552+00:00
-- url     : https://prove2.me/theorems/b68564c8-cec0-42d7-adc5-213c869096cb
-- title:
--   p. 34, as printed, fails — the ray 01^∞ is cofinal with 1^∞, yet its printed Gray code has infinitely many 1's
-- statement:
--   Let $x = 01^\infty$ (`prepend [false] oneRay`). Then $x$ is cofinal with $1^\infty$ (`IsCofinal`), and the printed Gray code of $x$, with digits $\bar x_i = \check x_1 + \ldots + \check x_i \bmod 2$ where $\check x_k = 1 - x_k$, has infinitely many digits equal to $1$: the set of $i$ with $\sum_{k \le i} (1 - x_k)$ odd is infinite. (The Lean indices start at $0$, so its $i$ is the paper's $i + 1$.)
--
--   Erschler and Zheng, p. 34: “The Grey code of $x$ is $\bar x = \bar x_1 \bar x_2 \ldots$ where $\bar x_i = \check x_1 + \ldots + \check x_i \mod 2$. Note that for $x$ cofinal with $1^\infty$, its Gray code $\bar x$ has only finitely many 1’s”
--
--   The statement contradicts the second sentence for the definition in the first. The definition used elsewhere is the corrected one of the bundle note (suffix sums), for which the formula $d_{\mathcal S}(x, y) = |\bar x - \bar y|$ holds (`ErschlerZheng.schreierDist_eq_abs_sub_grayCode_of_isCofinal`).
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 34, the Gray code as printed (prefix sums)

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk

namespace ErschlerZheng

theorem isCofinal_and_printed_gray_ones_infinite_prepend_false_oneRay :
    IsCofinal (prepend [false] oneRay) ∧
      {i : ℕ | (∑ k ∈ Finset.range (i + 1), (1 - (prepend [false] oneRay k).toNat)) % 2 = 1}.Infinite := by
  sorry

end ErschlerZheng
