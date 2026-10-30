-- Prove2me | Theorems.Thm_BitcoinBackboneProb_integral_roundY
-- name    : BitcoinBackboneProb.integral_roundY
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:13:42.138907+00:00
-- url     : https://prove2.me/theorems/92c02b2c-0d51-49e3-ad46-5d7e2936b130
-- title:
--   Expected uniquely successful rounds
-- statement:
--   $\int$ `roundY` $d(\text{roundMeasure}) = n p (1-p)^{n-1}$.
-- source:
--   J. Garay, A. Kiayias, N. Leonardos, The Bitcoin Backbone Protocol: Analysis and Applications, EUROCRYPT 2015 (full version ePrint 2014/765): https://eprint.iacr.org/2014/765, Definition 9 (typical execution), Theorem 10, the honest-majority assumption; W. Hoeffding (1963) for the concentration bound; the backbone mission BitcoinBackbone (Execution, Typical, chain growth, common prefix, chain quality)

import Definitions.Def_BitcoinBackboneProb
open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

theorem BitcoinBackboneProb.integral_roundY (n t : ℕ) (p : unitInterval) :
    ∫ ρ, (roundY ρ : ℝ) ∂(roundMeasure n t p) = n * p * (1 - (p : ℝ)) ^ (n - 1) := by sorry
