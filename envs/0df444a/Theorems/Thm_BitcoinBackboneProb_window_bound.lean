-- Prove2me | Theorems.Thm_BitcoinBackboneProb_window_bound
-- name    : BitcoinBackboneProb.window_bound
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:20:17.68878+00:00
-- url     : https://prove2.me/theorems/d604e9b2-e02c-40d1-b611-b39759e387b4
-- title:
--   A window fails typicality with exponentially small probability
-- statement:
--   For a window $[a, a+k]$ with $k \ge 1$ and $2tp \le (k-1)\,\text{margin}$: $P(\sum_{(a,a+k)} Y \le \sum_{[a,a+k]} Z) \le \exp(-2((k-1)\text{margin} - 2tp)^2 / ((k+1)(t+1)^2))$.
-- source:
--   J. Garay, A. Kiayias, N. Leonardos, The Bitcoin Backbone Protocol: Analysis and Applications, EUROCRYPT 2015 (full version ePrint 2014/765): https://eprint.iacr.org/2014/765, Definition 9 (typical execution), Theorem 10, the honest-majority assumption; W. Hoeffding (1963) for the concentration bound; the backbone mission BitcoinBackbone (Execution, Typical, chain growth, common prefix, chain quality)

import Definitions.Def_BitcoinBackboneProb
open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

theorem BitcoinBackboneProb.window_bound (n t : ℕ) (p : unitInterval) (a k : ℕ) (hk1 : 1 ≤ k)
    (hk : 2 * t * (p : ℝ) ≤ ((k : ℝ) - 1) * margin n t p) :
    (P n t p).real {ω | ∑ i ∈ Finset.Ioo a (a + k), Y ω i ≤ ∑ i ∈ Finset.Icc a (a + k), Z ω i} ≤
      Real.exp (-2 * (((k : ℝ) - 1) * margin n t p - 2 * t * p) ^ 2 /
        (((k : ℝ) + 1) * ((t : ℝ) + 1) ^ 2)) := by sorry
