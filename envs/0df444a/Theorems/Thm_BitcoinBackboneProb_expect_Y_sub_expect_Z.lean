-- Prove2me | Theorems.Thm_BitcoinBackboneProb_expect_Y_sub_expect_Z
-- name    : BitcoinBackboneProb.expect_Y_sub_expect_Z
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:17:30.410689+00:00
-- url     : https://prove2.me/theorems/8a98a7ce-e9cf-4baf-acce-1e1b2a1235f9
-- title:
--   E[Y] − E[Z] is the margin
-- statement:
--   $E[Y_r] - E[Z_r] =$ `margin n t p`.
-- source:
--   J. Garay, A. Kiayias, N. Leonardos, The Bitcoin Backbone Protocol: Analysis and Applications, EUROCRYPT 2015 (full version ePrint 2014/765): https://eprint.iacr.org/2014/765, Definition 9 (typical execution), Theorem 10, the honest-majority assumption; W. Hoeffding (1963) for the concentration bound; the backbone mission BitcoinBackbone (Execution, Typical, chain growth, common prefix, chain quality)

import Definitions.Def_BitcoinBackboneProb
open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

theorem BitcoinBackboneProb.expect_Y_sub_expect_Z (n t : ℕ) (p : unitInterval) (r : ℕ) :
    ∫ ω, (Y ω r : ℝ) ∂(P n t p) - ∫ ω, (Z ω r : ℝ) ∂(P n t p) = margin n t p := by sorry
