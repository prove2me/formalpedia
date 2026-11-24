-- Prove2me | Theorems.Thm_BB6Kit_nondegenerate
-- name    : BB6Kit.nondegenerate
-- status  : Open
-- author  : @alon yuval
-- created : 2026-11-23T22:13:11.699696+00:00
-- url     : https://prove2.me/theorems/170bb798-6da5-4764-8774-5532773b269e
-- title:
--   Non-degenerate case: $\log|\Lambda|\ge -2^{30}\log^3(4i)$ via the Mignotte–Voutier kit
-- statement:
--   Let $i\ge 2^{60}$, $1\le c\le 4i$, $2\le k\le 2i+2$, and $\Lambda\ne 0$. **Theorem (non-degenerate case).** If $2,c,3$ are multiplicatively independent, then $$\log|\Lambda|\ge -2^{30}\log^3(4i),\qquad \Lambda=(k-1)\log 2-i\log 3+\log c.$$ Proof via the Mignotte–Voutier kit with the explicit parameters of `BB6Kit`: the zero lemma gives $\Delta\ne0$; Propositions 3.7 and 3.9 give incompatible bounds unless $\Lambda'\ge 4^{-KL}$, and $KL\log4\le 2^{30}\log^3(4i)$.
-- source:
--   BB(6) Baker roadmap; Mignotte & Voutier (appendix by Laurent), A kit for linear forms in three logarithms, Math. Comp. (2023), arXiv:2205.08899, Theorem 2.1 route (Props 3.7, 3.9, 3.11).

import Mathlib
import Definitions.Def_BB6Delta
import Definitions.Def_BB6Kit

namespace BB6Kit
theorem nondegenerate (i k c : ℕ) (hi : 2 ^ 60 ≤ i) (hc : 0 < c) (hc4 : c ≤ 4 * i)
    (hk2 : 2 ≤ k) (hk : k ≤ 2 * i + 2)
    (hne : ((k : ℝ) - 1) * Real.log 2 - (i : ℝ) * Real.log 3 + Real.log (c : ℝ) ≠ 0) (hind : BB6Kit.MultIndep 2 c 3) :
    -(2 ^ 30 * Real.log (4 * (i : ℝ)) ^ 3) ≤ Real.log |((k : ℝ) - 1) * Real.log 2 - (i : ℝ) * Real.log 3 + Real.log (c : ℝ)| := by
  sorry
end BB6Kit
