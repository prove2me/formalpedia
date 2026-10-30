-- Prove2me | Theorems.Thm_BitcoinBackboneProb_expect_Z_lt_expect_Y
-- name    : BitcoinBackboneProb.expect_Z_lt_expect_Y
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:19:17.105426+00:00
-- url     : https://prove2.me/theorems/93aaa6d9-8abf-42f1-b7c3-7baeae654186
-- title:
--   Honest majority: adversarial blocks are strictly fewer than uniquely successful rounds in expectation
-- statement:
--   With $\delta, n, p > 0$ added: $E[Z_r] < E[Y_r]$.
-- source:
--   J. Garay, A. Kiayias, N. Leonardos, The Bitcoin Backbone Protocol: Analysis and Applications, EUROCRYPT 2015 (full version ePrint 2014/765): https://eprint.iacr.org/2014/765, Definition 9 (typical execution), Theorem 10, the honest-majority assumption; W. Hoeffding (1963) for the concentration bound; the backbone mission BitcoinBackbone (Execution, Typical, chain growth, common prefix, chain quality)

import Definitions.Def_BitcoinBackboneProb
open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

theorem BitcoinBackboneProb.expect_Z_lt_expect_Y (n t : ℕ) (p : unitInterval) (δ : ℝ)
    (hδ : 0 < δ) (hn : 0 < n) (hp0 : 0 < (p : ℝ))
    (ht : (t : ℝ) ≤ (1 - δ) * n) (hp : (n : ℝ) * p ≤ δ / 2) (r : ℕ) :
    ∫ ω, (Z ω r : ℝ) ∂(P n t p) < ∫ ω, (Y ω r : ℝ) ∂(P n t p) := by sorry
