-- Prove2me | Theorems.Thm_BFVBound_F_le_neg
-- name    : BFVBound.F_le_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-02T15:41:03.44021+00:00
-- url     : https://prove2.me/theorems/c21f4916-5fe0-481c-8bfa-da4190b8025a
-- title:
--   Product-side bound, negative range: $F(s)\\le 0.8488\\,s\\,(1+s^2/8)$ on $[-1,0]$
-- statement:
--   **Upper bound on the product expectation in the negative range.**
--
--   For $s\in[-1,0]$ (where $F(s)<0$, so this is a bound in the *favourable* direction for a product rounding),
--   $$F(s)\ \le\ 0.8488\,s\,\Bigl(1+\frac{s^{2}}{8}\Bigr).$$
--   Both factors are elementary: $G(x)\ge1+\frac{x}{8}$ for $x\ge0$ (drop all terms of the hypergeometric series
--   past the linear one) and $\frac{8}{3\pi}\ge0.8488$. Since $s<0$, multiplying the first inequality by
--   $c\,s$ and then applying $c\ge0.8488$ reverses the direction and gives the statement. The factor
--   $(1+s^2/8)$ matters: on the negative range it is what makes the certified min-max inequality of the
--   $0.614$ analysis tight enough to be provable.
-- source:
--   Anshu, Lee, Mousavi, Parekh, Soleimanifar, arXiv:2504.15276 Section 4.2 Eq. (17); Parekh-Thompson arXiv:2110.07781 Eq. (3); Brandao-Fernandes-Vallentin arXiv:0910.5765; G = 2F1(1/2,1/2;2;.) is the hypergeometric factor of the rank-three product rounding.

import Mathlib
import Definitions.Def_QuantumMaxCutBFVProductRounding
open scoped BigOperators

namespace BFVBound

theorem F_le_neg (s : ℝ) (hs1 : -1 ≤ s) (hs0 : s ≤ 0) :
    F s ≤ 0.8488 * s * (1 + s ^ 2 / 8) := by sorry

end BFVBound
