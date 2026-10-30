-- Prove2me | Theorems.Thm_BitcoinBackboneProb_expect_Z
-- name    : BitcoinBackboneProb.expect_Z
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:17:02.768316+00:00
-- url     : https://prove2.me/theorems/e4408eb2-0f63-46e8-b9b1-72d0d1cbb93b
-- title:
--   E[Z_r] = t p
-- statement:
--   For every round $r$.
-- source:
--   J. Garay, A. Kiayias, N. Leonardos, The Bitcoin Backbone Protocol: Analysis and Applications, EUROCRYPT 2015 (full version ePrint 2014/765): https://eprint.iacr.org/2014/765, Definition 9 (typical execution), Theorem 10, the honest-majority assumption; W. Hoeffding (1963) for the concentration bound; the backbone mission BitcoinBackbone (Execution, Typical, chain growth, common prefix, chain quality)

import Definitions.Def_BitcoinBackboneProb
open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

theorem BitcoinBackboneProb.expect_Z (n t : ℕ) (p : unitInterval) (r : ℕ) :
    ∫ ω, (Z ω r : ℝ) ∂(P n t p) = t * p := by sorry
