-- Prove2me | Theorems.Thm_BitcoinBackboneProb_typicalTrunc_failure_le
-- name    : BitcoinBackboneProb.typicalTrunc_failure_le
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:23:35.671416+00:00
-- url     : https://prove2.me/theorems/fdc64e0c-fd10-4e00-b9f9-2a52f268907c
-- title:
--   The induced execution is typical except with probability (L+1)² e^(−rate(λ+1))
-- statement:
--   For $\lambda \ge 2$, margin $> 0$ and $4tp \le (\lambda-3)$ margin: $P(\neg$`TypicalTrunc`$) \le (L+1)^2 e^{-\text{rate}(\lambda+1)}$, covering every window including those crossing the horizon.
-- source:
--   J. Garay, A. Kiayias, N. Leonardos, The Bitcoin Backbone Protocol: Analysis and Applications, EUROCRYPT 2015 (full version ePrint 2014/765): https://eprint.iacr.org/2014/765, Definition 9 (typical execution), Theorem 10, the honest-majority assumption; W. Hoeffding (1963) for the concentration bound; the backbone mission BitcoinBackbone (Execution, Typical, chain growth, common prefix, chain quality)

import Definitions.Def_BitcoinBackboneProb
open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

theorem BitcoinBackboneProb.typicalTrunc_failure_le (n t : ℕ) (p : unitInterval) (lam L : ℕ)
    (hlam : 2 ≤ lam) (hm : 0 < margin n t p)
    (hk : 4 * t * (p : ℝ) ≤ ((lam : ℝ) - 3) * margin n t p) :
    (P n t p).real {ω | ¬ TypicalTrunc ω lam L} ≤
      ((L : ℝ) + 1) ^ 2 * Real.exp (-rate n t p * ((lam : ℝ) + 1)) := by sorry
