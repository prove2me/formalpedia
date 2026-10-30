-- Prove2me | Theorems.Thm_BitcoinBackboneProb_window_bound_rate
-- name    : BitcoinBackboneProb.window_bound_rate
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:20:49.118978+00:00
-- url     : https://prove2.me/theorems/4e363790-0cf4-4192-bdb8-fe8994b26af2
-- title:
--   Window failure in rate form
-- statement:
--   If margin $> 0$ and $4tp \le (k-3)$ margin: the window fails with probability at most $\exp(-\text{rate}\cdot(k+1))$.
-- source:
--   J. Garay, A. Kiayias, N. Leonardos, The Bitcoin Backbone Protocol: Analysis and Applications, EUROCRYPT 2015 (full version ePrint 2014/765): https://eprint.iacr.org/2014/765, Definition 9 (typical execution), Theorem 10, the honest-majority assumption; W. Hoeffding (1963) for the concentration bound; the backbone mission BitcoinBackbone (Execution, Typical, chain growth, common prefix, chain quality)

import Definitions.Def_BitcoinBackboneProb
open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

theorem BitcoinBackboneProb.window_bound_rate (n t : ℕ) (p : unitInterval) (a k : ℕ)
    (hk1 : 1 ≤ k) (hm : 0 < margin n t p) (hk : 4 * t * (p : ℝ) ≤ ((k : ℝ) - 3) * margin n t p) :
    (P n t p).real {ω | ∑ i ∈ Finset.Ioo a (a + k), Y ω i ≤ ∑ i ∈ Finset.Icc a (a + k), Z ω i} ≤
      Real.exp (-rate n t p * ((k : ℝ) + 1)) := by sorry
