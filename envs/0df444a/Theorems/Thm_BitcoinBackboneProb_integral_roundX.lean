-- Prove2me | Theorems.Thm_BitcoinBackboneProb_integral_roundX
-- name    : BitcoinBackboneProb.integral_roundX
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:14:16.476179+00:00
-- url     : https://prove2.me/theorems/97f3bcec-552a-44d7-93d7-64963c849361
-- title:
--   Expected successful rounds
-- statement:
--   $\int$ `roundX` $= 1 - (1-p)^n$.
-- source:
--   J. Garay, A. Kiayias, N. Leonardos, The Bitcoin Backbone Protocol: Analysis and Applications, EUROCRYPT 2015 (full version ePrint 2014/765): https://eprint.iacr.org/2014/765, Definition 9 (typical execution), Theorem 10, the honest-majority assumption; W. Hoeffding (1963) for the concentration bound; the backbone mission BitcoinBackbone (Execution, Typical, chain growth, common prefix, chain quality)

import Definitions.Def_BitcoinBackboneProb
open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

theorem BitcoinBackboneProb.integral_roundX (n t : ℕ) (p : unitInterval) :
    ∫ ρ, (roundX ρ : ℝ) ∂(roundMeasure n t p) = 1 - (1 - (p : ℝ)) ^ n := by sorry
