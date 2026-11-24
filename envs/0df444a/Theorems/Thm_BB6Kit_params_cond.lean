-- Prove2me | Theorems.Thm_BB6Kit_params_cond
-- name    : BB6Kit.params_cond
-- status  : Proved
-- author  : @alon yuval
-- created : 2026-11-23T22:13:04.28055+00:00
-- url     : https://prove2.me/theorems/b54ccefc-bc37-4741-9f85-364b52e73c0e
-- title:
--   Explicit kit parameters for $i\ge 2^{60}$: conditions (2.7), (2.9)–(2.13), not (2.14)
-- statement:
--   **Lemma (parameter conditions).** For every $n\ge 60$, the explicit family of definition `BB6Kit` ($K=2^{23}n^2$, $L=8n$, $R_1=T_1=K/8$, $S_1=80$, $R_2=T_2=K/64$, $S_2=S_3=2^{15}n$, $R_3=T_3=K/32$, $\chi=M_0/\sqrt{V_1}$) satisfies:
--
--   - $K\ge3$, $L\ge5$, $N\le RST$, positivity, and (2.7);
--   - (2.9) with this $\chi$;
--   - the product forms of (2.10)–(2.13);
--   - $\max(T_1,T_2)<2^n$, which excludes (2.14) when $b_3=i\ge 2^n$;
--   - $LT\le 2^n$;
--   - $KL\log 4\le 2^{30}((n+2)\log 2)^3$.
--
--   Elementary arithmetic; checked numerically for all $60\le n\le 400$ and sample $n$ up to $10^5$.
-- source:
--   Mignotte & Voutier (appendix by Laurent), A kit for linear forms in three logarithms, Math. Comp. (2023), arXiv:2205.08899, Theorem 2.1 conditions (2.7), (2.9)-(2.14); explicit parameter family new (BB(6) Baker roadmap).

import Mathlib
import Definitions.Def_BB6Delta
import Definitions.Def_BB6Kit

namespace BB6Kit
theorem params_cond (n : ℕ) (hn : 60 ≤ n) :
    3 ≤ (BB6Kit.fK n) ∧ 5 ≤ (BB6Kit.fL n) ∧ (BB6Kit.fN n) ≤ (BB6Kit.fR n) * (BB6Kit.fS n) * (BB6Kit.fR n) ∧
    (0 < (BB6Kit.fR1 n) ∧ 0 < (BB6Kit.fS1 n) ∧ 0 < (BB6Kit.fR1 n) ∧ 0 < (BB6Kit.fR2 n) ∧ 0 < (BB6Kit.fS2 n) ∧ 0 < (BB6Kit.fR2 n) ∧ 0 < (BB6Kit.fR3 n) ∧ 0 < (BB6Kit.fS3 n) ∧ 0 < (BB6Kit.fR3 n)) ∧
    ((BB6Kit.fR1 n) + (BB6Kit.fR2 n) + (BB6Kit.fR3 n) < (BB6Kit.fR n) ∧ (BB6Kit.fS1 n) + (BB6Kit.fS2 n) + (BB6Kit.fS3 n) < (BB6Kit.fS n) ∧ (BB6Kit.fR1 n) + (BB6Kit.fR2 n) + (BB6Kit.fR3 n) < (BB6Kit.fR n)) ∧ 0 < (BB6Kit.fChi n) ∧
    ((BB6Kit.fK n) : ℝ) * (max (max (((BB6Kit.fR1 n) : ℝ) + (BB6Kit.fS1 n) + 1) (((BB6Kit.fS1 n) : ℝ) + (BB6Kit.fR1 n) + 1)) (max (((BB6Kit.fR1 n) : ℝ) + (BB6Kit.fR1 n) + 1) ((BB6Kit.fChi n) * Real.sqrt ((((BB6Kit.fR1 n) : ℝ) + 1) * (((BB6Kit.fS1 n) : ℝ) + 1) * (((BB6Kit.fR1 n) : ℝ) + 1))))) < ((((BB6Kit.fR1 n) : ℝ) + 1) * (((BB6Kit.fS1 n) : ℝ) + 1) * (((BB6Kit.fR1 n) : ℝ) + 1)) ∧
    (BB6Kit.fL n) < ((BB6Kit.fR1 n) + 1) * ((BB6Kit.fS1 n) + 1) * ((BB6Kit.fR1 n) + 1) ∧ 2 * (BB6Kit.fK n) * (BB6Kit.fL n) < ((BB6Kit.fR2 n) + 1) * ((BB6Kit.fS2 n) + 1) * ((BB6Kit.fR2 n) + 1) ∧
    (BB6Kit.fK n) ^ 2 < ((BB6Kit.fR2 n) + 1) * ((BB6Kit.fS2 n) + 1) * ((BB6Kit.fR2 n) + 1) ∧ 3 * (BB6Kit.fK n) ^ 2 * (BB6Kit.fL n) < ((BB6Kit.fR3 n) + 1) * ((BB6Kit.fS3 n) + 1) * ((BB6Kit.fR3 n) + 1) ∧
    max (BB6Kit.fR1 n) (BB6Kit.fR2 n) < 2 ^ n ∧ (BB6Kit.fL n) * (BB6Kit.fR n) ≤ 2 ^ n ∧
    ((BB6Kit.fK n) : ℝ) * (BB6Kit.fL n) * Real.log 4 ≤ 2 ^ 30 * (((n : ℝ) + 2) * Real.log 2) ^ 3 := by
  sorry
end BB6Kit
