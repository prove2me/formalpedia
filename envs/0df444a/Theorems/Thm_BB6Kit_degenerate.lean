-- Prove2me | Theorems.Thm_BB6Kit_degenerate
-- name    : BB6Kit.degenerate
-- status  : Open
-- author  : @alon yuval
-- created : 2026-11-23T22:13:04.522973+00:00
-- url     : https://prove2.me/theorems/8ed224cb-f24c-4322-b2c3-5fb53950c7c8
-- title:
--   Degenerate case $c=2^a3^b$: $\log|\Lambda|\ge -2^{30}\log^3(4i)$
-- statement:
--   Let $i\ge 2^{60}$, $1\le c\le 4i$, $2\le k\le 2i+2$, and $\Lambda\ne 0$. **Theorem (degenerate case).** If $c=2^a3^b$, then $$\log|\Lambda|\ge -2^{30}\log^3(4i),\qquad \Lambda=(k-1)\log 2-i\log 3+\log c.$$ Then $\Lambda=(k-1+a)\log2-(i-b)\log3$ is a linear form in two logarithms, bounded by `BB6Kit.laurent_23`.
-- source:
--   BB(6) Baker roadmap; uses Laurent (2008) Corollary 2 via BB6Kit.laurent_23.

import Mathlib
import Definitions.Def_BB6Delta
import Definitions.Def_BB6Kit

namespace BB6Kit
theorem degenerate (i k c : ℕ) (hi : 2 ^ 60 ≤ i) (hc : 0 < c) (hc4 : c ≤ 4 * i)
    (hk2 : 2 ≤ k) (hk : k ≤ 2 * i + 2)
    (hne : ((k : ℝ) - 1) * Real.log 2 - (i : ℝ) * Real.log 3 + Real.log (c : ℝ) ≠ 0) (hsm : ∃ a b : ℕ, c = 2 ^ a * 3 ^ b) :
    -(2 ^ 30 * Real.log (4 * (i : ℝ)) ^ 3) ≤ Real.log |((k : ℝ) - 1) * Real.log 2 - (i : ℝ) * Real.log 3 + Real.log (c : ℝ)| := by
  sorry
end BB6Kit
