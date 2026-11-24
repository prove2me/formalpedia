-- Prove2me | Theorems.Thm_BB6Kit_kit_bound
-- name    : BB6Kit.kit_bound
-- status  : Open
-- author  : @alon yuval
-- created : 2026-11-23T22:13:10.472824+00:00
-- url     : https://prove2.me/theorems/37d47a77-299d-4986-abda-8cd9ac1a0ad8
-- title:
--   Linear form in $\log 2,\log 3,\log c$: $\log|\Lambda|\ge -2^{30}\log^3(4i)$ (Mignotte–Voutier kit)
-- statement:
--   Let $i\ge 2^{60}$, $1\le c\le 4i$, $2\le k\le 2i+2$, and $\Lambda\ne 0$. **Theorem.** $$\log|\Lambda|\ge -2^{30}\log^3(4i),\qquad \Lambda=(k-1)\log 2-i\log 3+\log c.$$
--
--   This is an explicit lower bound for a linear form in three logarithms ($\log 2,\log 3,\log c$, $c$ varying with $i$). It follows from the Mignotte–Voutier kit (non-degenerate case) and Laurent's two-logarithm bound (degenerate case $c=2^a3^b$). It is weaker than `BB6Baker.bw_instance` (cubic rather than quadratic in $\log i$), which the kit cannot give, but strong enough for the Pillai gap `BB6Baker.pillai_gap` (with `BB6Kit.numerics`). This route avoids Matveev's and Baker–Wüstholz's theorems.
--
--   *Baker-free.* The route uses only Theorem 2.1 of the kit in its proved form (Props 3.7, 3.9, 3.11 and Section 4, which use interpolation determinants, Schwarz's lemma, Liouville and Gouillon's zero estimate), with parameters given explicitly as functions of $n=\lfloor\log_2 i\rfloor$ for every $n\ge 60$. The kit's application step (2) (Section 1.2), which uses Matveev only to get an a priori bound on the coefficients, is not needed. The degenerate case uses Laurent's two-logarithm interpolation-determinant bound. No Matveev or Baker–Wüstholz input.
-- source:
--   BB(6) machine 1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB--- (non-halting reduction in rwst/bbchallenge, CC0); Mignotte & Voutier (appendix by Laurent), A kit for linear forms in three logarithms, Math. Comp. (2023), arXiv:2205.08899; Laurent, Acta Arith. 133 (2008).

import Mathlib
import Definitions.Def_BB6Delta
import Definitions.Def_BB6Kit

namespace BB6Kit
theorem kit_bound (i k c : ℕ) (hi : 2 ^ 60 ≤ i) (hc : 0 < c) (hc4 : c ≤ 4 * i)
    (hk2 : 2 ≤ k) (hk : k ≤ 2 * i + 2)
    (hne : ((k : ℝ) - 1) * Real.log 2 - (i : ℝ) * Real.log 3 + Real.log (c : ℝ) ≠ 0) :
    -(2 ^ 30 * Real.log (4 * (i : ℝ)) ^ 3) ≤ Real.log |((k : ℝ) - 1) * Real.log 2 - (i : ℝ) * Real.log 3 + Real.log (c : ℝ)| := by
  sorry
end BB6Kit
