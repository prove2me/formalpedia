-- Prove2me | Theorems.Thm_ErschlerZheng_schreierDist_le_two_pow_mul_schreierDist_shiftRay_add_of_isCofinal
-- name    : ErschlerZheng.schreierDist_le_two_pow_mul_schreierDist_shiftRay_add_of_isCofinal
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T01:26:12.926345+00:00
-- url     : https://prove2.me/theorems/71a21a98-550c-434e-a80b-684b7c459b9b
-- title:
--   Fact 7.4 — for x, y cofinal with 1^∞, d_𝒮(x, y) ⩽ 2^n d_𝒮(𝔰^n x, 𝔰^n y) + 2^n − 1
-- statement:
--   For every string $\omega \in \{\mathbf 0, \mathbf 1, \mathbf 2\}^{\mathbb N}$, all rays $x, y$ cofinal with $1^\infty$ (`IsCofinal`) and every $n \in \mathbb N$,
--   $$d_{\mathcal S_\omega}(x, y) \le 2^n\, d_{\mathcal S_\omega}(\mathfrak s^n x, \mathfrak s^n y) + 2^n - 1,$$
--   where $\mathfrak s^n x = x_{n+1}x_{n+2}\ldots$ (`shiftRay`) and $d_{\mathcal S_\omega}$ is the Schreier distance (`schreierDist`) for the same $\omega$ on both sides.
--
--   Erschler and Zheng, p. 35, Fact 7.4: “Let $x, y$ be two points cofinal with $1^\infty$. Denote by $\mathfrak s$ the shift on strings. Then $d_{\mathcal S}(x, y) \leqslant 2^n d_{\mathcal S}(\mathfrak s^n x, \mathfrak s^n y) + 2^n - 1$.”
--
--   The paper's $d_{\mathcal S}$ carries no $\omega$ because the distance does not depend on it ([`ErschlerZheng.orbitOne_eq_and_adjacent_iff_and_card_eq_and_schreierDist_eq`](https://prove2.me/theorems/407877ac-caa9-4735-bc30-3d651039d391)); the statement uses one $\omega$ throughout.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 35, Fact 7.4

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk

namespace ErschlerZheng

theorem schreierDist_le_two_pow_mul_schreierDist_shiftRay_add_of_isCofinal (ω : ℕ → Fin 3)
    (x y : Ray) (hx : IsCofinal x) (hy : IsCofinal y) (n : ℕ) :
    schreierDist ω x y ≤ 2 ^ n * schreierDist ω (shiftRay x n) (shiftRay y n) + 2 ^ n - 1 := by
  sorry

end ErschlerZheng
