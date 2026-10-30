-- Prove2me | Theorems.Thm_BitcoinBackboneProb_typicalOn_failure_le_of_window
-- name    : BitcoinBackboneProb.typicalOn_failure_le_of_window
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:21:22.034598+00:00
-- url     : https://prove2.me/theorems/17831ef0-39df-40f1-8d69-cae076a22edf
-- title:
--   Union bound over windows
-- statement:
--   If every window of length at least $\lambda \ge 1$ fails with probability at most $\beta$, then $P(\neg$`TypicalOn ω lam L`$) \le L^2 \beta$.
-- source:
--   J. Garay, A. Kiayias, N. Leonardos, The Bitcoin Backbone Protocol: Analysis and Applications, EUROCRYPT 2015 (full version ePrint 2014/765): https://eprint.iacr.org/2014/765, Definition 9 (typical execution), Theorem 10, the honest-majority assumption; W. Hoeffding (1963) for the concentration bound; the backbone mission BitcoinBackbone (Execution, Typical, chain growth, common prefix, chain quality)

import Definitions.Def_BitcoinBackboneProb
open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

theorem BitcoinBackboneProb.typicalOn_failure_le_of_window (n t : ℕ) (p : unitInterval)
    (lam L : ℕ) (hlam : 1 ≤ lam) (β : ℝ)
    (hβ : ∀ a k : ℕ, lam ≤ k → (P n t p).real
      {ω | ∑ i ∈ Finset.Ioo a (a + k), Y ω i ≤ ∑ i ∈ Finset.Icc a (a + k), Z ω i} ≤ β) :
    (P n t p).real {ω | ¬ TypicalOn ω lam L} ≤ (L : ℝ) ^ 2 * β := by sorry
