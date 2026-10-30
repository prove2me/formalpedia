-- Prove2me | Theorems.Thm_BitcoinBackboneProb_sets_hoeffding
-- name    : BitcoinBackboneProb.sets_hoeffding
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:19:45.471908+00:00
-- url     : https://prove2.me/theorems/46e37558-bbff-427b-9721-80e13e346b8b
-- title:
--   Hoeffding's inequality for the adversary's lead on finite sets of rounds
-- statement:
--   For finite $T \subseteq S$ and $j \ge 0$ with $\varepsilon = j + |T| E[Y] - |S| E[Z] \ge 0$: $P(\sum_T Y + j \le \sum_S Z) \le \exp(-2\varepsilon^2 / (|S|(t+1)^2))$.
-- source:
--   J. Garay, A. Kiayias, N. Leonardos, The Bitcoin Backbone Protocol: Analysis and Applications, EUROCRYPT 2015 (full version ePrint 2014/765): https://eprint.iacr.org/2014/765, Definition 9 (typical execution), Theorem 10, the honest-majority assumption; W. Hoeffding (1963) for the concentration bound; the backbone mission BitcoinBackbone (Execution, Typical, chain growth, common prefix, chain quality)

import Definitions.Def_BitcoinBackboneProb
open BitcoinBackboneProb BitcoinBackbone
open MeasureTheory ProbabilityTheory

theorem BitcoinBackboneProb.sets_hoeffding (n t : ℕ) (p : unitInterval) (S T : Finset ℕ)
    (hTS : T ⊆ S) (j : ℕ)
    (hε : 0 ≤ (j : ℝ) + T.card * (n * p * (1 - (p : ℝ)) ^ (n - 1)) - S.card * (t * p)) :
    (P n t p).real {ω | ∑ i ∈ T, Y ω i + j ≤ ∑ i ∈ S, Z ω i} ≤
      Real.exp (-2 * ((j : ℝ) + T.card * (n * p * (1 - (p : ℝ)) ^ (n - 1)) - S.card * (t * p)) ^ 2
        / (S.card * ((t : ℝ) + 1) ^ 2)) := by sorry
