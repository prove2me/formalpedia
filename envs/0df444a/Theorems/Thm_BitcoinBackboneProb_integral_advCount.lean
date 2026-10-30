-- Prove2me | Theorems.Thm_BitcoinBackboneProb_integral_advCount
-- name    : BitcoinBackboneProb.integral_advCount
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:14:53.209814+00:00
-- url     : https://prove2.me/theorems/d78c4bd2-3301-4d37-b92e-e26774660ea9
-- title:
--   Expected adversarial blocks per round
-- statement:
--   $\int$ `advCount` $= t p$.
-- source:
--   J. Garay, A. Kiayias, N. Leonardos, The Bitcoin Backbone Protocol: Analysis and Applications, EUROCRYPT 2015 (full version ePrint 2014/765): https://eprint.iacr.org/2014/765, Definition 9 (typical execution), Theorem 10, the honest-majority assumption; W. Hoeffding (1963) for the concentration bound; the backbone mission BitcoinBackbone (Execution, Typical, chain growth, common prefix, chain quality)

import Definitions.Def_BitcoinBackboneProb
open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

theorem BitcoinBackboneProb.integral_advCount (n t : ℕ) (p : unitInterval) :
    ∫ ρ, (advCount ρ : ℝ) ∂(roundMeasure n t p) = t * p := by sorry
