-- Prove2me | Theorems.Thm_BB6Kit_laurent_23
-- name    : BB6Kit.laurent_23
-- status  : Open
-- author  : @alon yuval
-- created : 2026-11-23T22:13:00.331807+00:00
-- url     : https://prove2.me/theorems/75b7396e-56e1-4956-ba0f-d279d557714a
-- title:
--   Laurent's two-logarithm bound for $|b_2\log 3-b_1\log 2|$ (Corollary 2, 2008)
-- statement:
--   Laurent's explicit lower bound for linear forms in two logarithms, specialised to $\log 2$ and $\log 3$. **Theorem.** For all positive integers $b_1,b_2$, $$\log\bigl|b_2\log 3-b_1\log 2\bigr| \ge -25.2\,(\log 3)\,\max\Bigl(\log\Bigl(\frac{b_1}{\log 3}+b_2\Bigr)+0.38,\; 10\Bigr)^2.$$
--
--   This is Corollary 2 of Laurent (2008) with $\alpha_1=2$, $\alpha_2=3$, $D=1$, $\log B_1=1$, $\log B_2=\log 3$ (so $b'=b_1/\log 3+b_2$). It handles the degenerate case $c=2^a3^b$ of `BB6Kit.kit_bound`.
-- source:
--   M. Laurent, Linear forms in two logarithms and interpolation determinants II, Acta Arith. 133 (2008) 325–348, Corollary 2 (m=10, C2=25.2), with alpha1=2, alpha2=3, D=1. Statement as transcribed in arXiv:2002.11366 (Prop. 2.1) and arXiv:2604.18991 (Prop. 6.1); the primary text was not checked directly.

import Mathlib
import Definitions.Def_BB6Delta
import Definitions.Def_BB6Kit

namespace BB6Kit
theorem laurent_23 (b1 b2 : ℕ) (hb1 : 0 < b1) (hb2 : 0 < b2) :
    -(25.2 * Real.log 3 * (max (Real.log ((b1 : ℝ) / Real.log 3 + b2) + 0.38) 10) ^ 2) ≤
      Real.log |(b2 : ℝ) * Real.log 3 - (b1 : ℝ) * Real.log 2| := by
  sorry
end BB6Kit
