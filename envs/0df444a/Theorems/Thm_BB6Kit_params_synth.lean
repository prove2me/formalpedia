-- Prove2me | Theorems.Thm_BB6Kit_params_synth
-- name    : BB6Kit.params_synth
-- status  : Proved
-- author  : @alon yuval
-- created : 2026-11-23T22:12:56.956913+00:00
-- url     : https://prove2.me/theorems/f0d739e8-19de-46e0-83c5-13ca4b2ef4c4
-- title:
--   Explicit kit parameters: the Prop. 3.7 upper bound falls below the Prop. 3.9 lower bound
-- statement:
--   **Lemma (synthesis inequality).** Let $n\ge 60$, $2^n\le i<2^{n+1}$, $1\le c\le 4i$, $2\le k\le 2i+2$, with the parameter family of `BB6Kit`, $\rho=4$, $\alpha=(2,c,3)$, $b=(k-1,1,i)$. Then
--   $$5\sum_j G_j\log\alpha_j+\log N!+N\log2+\tfrac{N(K-1)}{3}\log b+0.001<\tfrac{N^2}{2K}\Bigl(1-\tfrac{2}{3L}-\tfrac{2}{3KL}-\tfrac{1}{3L^2}-\tfrac{16}{3K^2L}\Bigr)\log 4.$$
--
--   This is exactly what makes the upper bound of `BB6Kit.prop37` ($\rho=4$) fall below the lower bound of `BB6Kit.prop39_int`, i.e. the inequality behind Proposition 3.10 / condition (2.8) of the kit. Checked numerically with relative margin 19–27% (for $60\le n\le 400$ and sample $n$ up to $10^5$).
-- source:
--   Mignotte & Voutier (appendix by Laurent), A kit for linear forms in three logarithms, Math. Comp. (2023), arXiv:2205.08899, Propositions 3.7, 3.9, 3.10 (synthesis); explicit parameter family new.

import Mathlib
import Definitions.Def_BB6Delta
import Definitions.Def_BB6Kit

namespace BB6Kit
theorem params_synth (n i k c : ℕ) (hn : 60 ≤ n) (hi : 2 ^ n ≤ i) (hi' : i < 2 ^ (n + 1))
    (hc : 0 < c) (hc4 : c ≤ 4 * i) (hk2 : 2 ≤ k) (hk : k ≤ 2 * i + 2) :
    5 * (BB6Kit.GK (BB6Kit.fN n) (BB6Kit.fL n) (BB6Kit.fR n) (BB6Kit.fS n) (BB6Kit.fR n) (BB6Kit.fR n) * Real.log ((2 : ℕ) : ℝ) + BB6Kit.GK (BB6Kit.fN n) (BB6Kit.fL n) (BB6Kit.fR n) (BB6Kit.fS n) (BB6Kit.fR n) (BB6Kit.fS n) * Real.log ((c) : ℝ) + BB6Kit.GK (BB6Kit.fN n) (BB6Kit.fL n) (BB6Kit.fR n) (BB6Kit.fS n) (BB6Kit.fR n) (BB6Kit.fR n) * Real.log ((3 : ℕ) : ℝ)) + Real.log ((BB6Kit.fN n).factorial : ℝ) + ((BB6Kit.fN n) : ℝ) * Real.log 2 + ((BB6Kit.fN n) : ℝ) * (((BB6Kit.fK n) : ℝ) - 1) / 3 * Real.log (BB6Kit.bK (BB6Kit.fK n) (BB6Kit.fR n) (BB6Kit.fS n) (BB6Kit.fR n) ((k - 1 : ℕ) / Nat.gcd (k - 1 : ℕ) (i)) ((i) / Nat.gcd (k - 1 : ℕ) (i)) ((1 : ℕ) / Nat.gcd (1 : ℕ) (i)) ((i) / Nat.gcd (1 : ℕ) (i))) + 0.001 <
      ((BB6Kit.fN n) : ℝ) ^ 2 / (2 * ((BB6Kit.fK n) : ℝ)) * (1 - 2 / (3 * ((BB6Kit.fL n) : ℝ)) - 2 / (3 * ((BB6Kit.fK n) : ℝ) * (BB6Kit.fL n)) - 1 / (3 * ((BB6Kit.fL n) : ℝ) ^ 2) -
        16 / (3 * ((BB6Kit.fK n) : ℝ) ^ 2 * (BB6Kit.fL n))) * Real.log 4 := by
  sorry
end BB6Kit
