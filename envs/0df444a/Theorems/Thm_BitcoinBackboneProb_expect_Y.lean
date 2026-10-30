-- Prove2me | Theorems.Thm_BitcoinBackboneProb_expect_Y
-- name    : BitcoinBackboneProb.expect_Y
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:15:37.79026+00:00
-- url     : https://prove2.me/theorems/b9d20561-f7ff-4ade-b3b4-42300f9065c0
-- title:
--   E[Y_r] = n p (1-p)^(n-1)
-- statement:
--   For every round $r$: $E[Y_r] = n p (1-p)^{n-1}$.
-- source:
--   J. Garay, A. Kiayias, N. Leonardos, The Bitcoin Backbone Protocol: Analysis and Applications, EUROCRYPT 2015 (full version ePrint 2014/765): https://eprint.iacr.org/2014/765, Definition 9 (typical execution), Theorem 10, the honest-majority assumption; W. Hoeffding (1963) for the concentration bound; the backbone mission BitcoinBackbone (Execution, Typical, chain growth, common prefix, chain quality)

import Definitions.Def_BitcoinBackboneProb
open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

theorem BitcoinBackboneProb.expect_Y (n t : ℕ) (p : unitInterval) (r : ℕ) :
    ∫ ω, (Y ω r : ℝ) ∂(P n t p) = n * p * (1 - (p : ℝ)) ^ (n - 1) := by sorry
