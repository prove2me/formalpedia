-- Prove2me | Theorems.Thm_BitcoinBackboneProb_expect_X
-- name    : BitcoinBackboneProb.expect_X
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:16:31.989405+00:00
-- url     : https://prove2.me/theorems/44852ece-48df-45e8-9dcb-4322ca25aa0c
-- title:
--   E[X_r] = 1 - (1-p)^n
-- statement:
--   For every round $r$.
-- source:
--   J. Garay, A. Kiayias, N. Leonardos, The Bitcoin Backbone Protocol: Analysis and Applications, EUROCRYPT 2015 (full version ePrint 2014/765): https://eprint.iacr.org/2014/765, Definition 9 (typical execution), Theorem 10, the honest-majority assumption; W. Hoeffding (1963) for the concentration bound; the backbone mission BitcoinBackbone (Execution, Typical, chain growth, common prefix, chain quality)

import Definitions.Def_BitcoinBackboneProb
open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

theorem BitcoinBackboneProb.expect_X (n t : ℕ) (p : unitInterval) (r : ℕ) :
    ∫ ω, (X ω r : ℝ) ∂(P n t p) = 1 - (1 - (p : ℝ)) ^ n := by sorry
