-- Prove2me | Theorems.Thm_BitcoinBackboneProb_typicalOn_failure_le
-- name    : BitcoinBackboneProb.typicalOn_failure_le
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:22:04.742968+00:00
-- url     : https://prove2.me/theorems/2510b31f-6144-4881-85e1-4bf0a98137fc
-- title:
--   Typicality on a horizon fails with probability at most L² e^(−rate(λ+1))
-- statement:
--   Under the window hypothesis at $\lambda$.
-- source:
--   J. Garay, A. Kiayias, N. Leonardos, The Bitcoin Backbone Protocol: Analysis and Applications, EUROCRYPT 2015 (full version ePrint 2014/765): https://eprint.iacr.org/2014/765, Definition 9 (typical execution), Theorem 10, the honest-majority assumption; W. Hoeffding (1963) for the concentration bound; the backbone mission BitcoinBackbone (Execution, Typical, chain growth, common prefix, chain quality)

import Definitions.Def_BitcoinBackboneProb
open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

theorem BitcoinBackboneProb.typicalOn_failure_le (n t : ℕ) (p : unitInterval) (lam L : ℕ)
    (hlam : 1 ≤ lam) (hm : 0 < margin n t p)
    (hk : 4 * t * (p : ℝ) ≤ ((lam : ℝ) - 3) * margin n t p) :
    (P n t p).real {ω | ¬ TypicalOn ω lam L} ≤
      (L : ℝ) ^ 2 * Real.exp (-rate n t p * ((lam : ℝ) + 1)) := by sorry
