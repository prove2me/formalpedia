-- Prove2me | Theorems.Thm_BitcoinBackboneProb_typicalOn_prob_ge
-- name    : BitcoinBackboneProb.typicalOn_prob_ge
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:22:39.337783+00:00
-- url     : https://prove2.me/theorems/effe3643-73ba-4c6c-8463-031a2da65fb1
-- title:
--   Typicality on a horizon holds with probability at least 1 − L² e^(−rate(λ+1))
-- statement:
--   The complement of `typicalOn_failure_le`.
-- source:
--   J. Garay, A. Kiayias, N. Leonardos, The Bitcoin Backbone Protocol: Analysis and Applications, EUROCRYPT 2015 (full version ePrint 2014/765): https://eprint.iacr.org/2014/765, Definition 9 (typical execution), Theorem 10, the honest-majority assumption; W. Hoeffding (1963) for the concentration bound; the backbone mission BitcoinBackbone (Execution, Typical, chain growth, common prefix, chain quality)

import Definitions.Def_BitcoinBackboneProb
open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

theorem BitcoinBackboneProb.typicalOn_prob_ge (n t : ℕ) (p : unitInterval) (lam L : ℕ)
    (hlam : 1 ≤ lam) (hm : 0 < margin n t p)
    (hk : 4 * t * (p : ℝ) ≤ ((lam : ℝ) - 3) * margin n t p) :
    1 - (L : ℝ) ^ 2 * Real.exp (-rate n t p * ((lam : ℝ) + 1)) ≤
      (P n t p).real {ω | TypicalOn ω lam L} := by sorry
