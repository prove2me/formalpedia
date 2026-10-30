-- Prove2me | Theorems.Thm_BitcoinBackboneProb_expect_Z_add_le_expect_Y
-- name    : BitcoinBackboneProb.expect_Z_add_le_expect_Y
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:18:27.240557+00:00
-- url     : https://prove2.me/theorems/437f4620-0362-4dc9-8f32-f482703a1da3
-- title:
--   Honest majority: E[Z] + δpn/2 ≤ E[Y]
-- statement:
--   Under the same conditions, for every round.
-- source:
--   J. Garay, A. Kiayias, N. Leonardos, The Bitcoin Backbone Protocol: Analysis and Applications, EUROCRYPT 2015 (full version ePrint 2014/765): https://eprint.iacr.org/2014/765, Definition 9 (typical execution), Theorem 10, the honest-majority assumption; W. Hoeffding (1963) for the concentration bound; the backbone mission BitcoinBackbone (Execution, Typical, chain growth, common prefix, chain quality)

import Definitions.Def_BitcoinBackboneProb
open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

theorem BitcoinBackboneProb.expect_Z_add_le_expect_Y (n t : ℕ) (p : unitInterval) (δ : ℝ)
    (ht : (t : ℝ) ≤ (1 - δ) * n) (hp : (n : ℝ) * p ≤ δ / 2) (r : ℕ) :
    ∫ ω, (Z ω r : ℝ) ∂(P n t p) + δ * p * n / 2 ≤ ∫ ω, (Y ω r : ℝ) ∂(P n t p) := by sorry
