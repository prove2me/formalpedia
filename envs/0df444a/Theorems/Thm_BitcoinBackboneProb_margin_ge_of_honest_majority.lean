-- Prove2me | Theorems.Thm_BitcoinBackboneProb_margin_ge_of_honest_majority
-- name    : BitcoinBackboneProb.margin_ge_of_honest_majority
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:18:00.305973+00:00
-- url     : https://prove2.me/theorems/5d9534de-01ef-4a37-8d88-d025d0fc0502
-- title:
--   Honest majority gives a positive margin
-- statement:
--   If $t \le (1-\delta) n$ and $n p \le \delta/2$: `margin n t p` $\ge \delta p n / 2$.
-- source:
--   J. Garay, A. Kiayias, N. Leonardos, The Bitcoin Backbone Protocol: Analysis and Applications, EUROCRYPT 2015 (full version ePrint 2014/765): https://eprint.iacr.org/2014/765, Definition 9 (typical execution), Theorem 10, the honest-majority assumption; W. Hoeffding (1963) for the concentration bound; the backbone mission BitcoinBackbone (Execution, Typical, chain growth, common prefix, chain quality)

import Definitions.Def_BitcoinBackboneProb
open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

theorem BitcoinBackboneProb.margin_ge_of_honest_majority (n t : ℕ) (p : unitInterval) (δ : ℝ)
    (ht : (t : ℝ) ≤ (1 - δ) * n) (hp : (n : ℝ) * p ≤ δ / 2) :
    δ * p * n / 2 ≤ margin n t p := by sorry
