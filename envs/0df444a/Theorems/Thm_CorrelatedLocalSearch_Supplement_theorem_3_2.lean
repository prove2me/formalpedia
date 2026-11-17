-- Prove2me | Theorems.Thm_CorrelatedLocalSearch_Supplement_theorem_3_2
-- name    : CorrelatedLocalSearch.Supplement.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:05:18.994851+00:00
-- url     : https://prove2.me/theorems/347280b8-9a60-4e46-98fe-6b056e15d5d6
-- title:
--   Theorem 3.2 — equal prefix sums, different robustness
-- statement:
--   With $P(0)=15/16$, $P(1)=1/16$ and $\mathcal Q=\mathcal Q_{1/2,1}$, for every $n\ge1$ the bad order has worst survival probability one at time $8n$, while the good order lies between $(15/16)^{4n}$ and $\frac98(225/256)^n<1$. One source separates both orders. The lower bound holds for every selector, the good order is minimax at every deadline, and all selectors have identical independent stopping laws and both powered prefix sums at every depth and exponent.
--
--   Differences from the source:
--   - encoding: worst probabilities written as nonnegative real quantities → `ENNReal`; reason: exact nonnegative encoding
-- source:
--   Xu, Local Search with Correlated Randomness, arXiv:2607.17469 (sha256 17e00d69…), Theorem 3.2, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_CorrelatedLocalSearch_Supplement_RetryTasks

set_option autoImplicit false

namespace CorrelatedLocalSearch.Supplement

open MeasureTheory
open scoped ENNReal BigOperators

/-- Xu, arXiv:2607.17469 (sha256 17e00d69…), Theorem 3.2, p.8 (PDF p.10).
The two fixed orders have identical independent data but sharply different robust deadline tails;
one source separates both, the lower bound is selector-uniform, and `Lambda_B` is minimax at every
deadline. -/
theorem theorem_3_2 (n : Nat) (hn : 1 ≤ n) :
    let M := separationRetryModel n
    let A := orderASelector n
    let B := orderBSelector n
    worstProbability separationPi (1 / 2 : Real) 1 (retrySurvivalEvent M A (8 * n)) = 1 ∧
    ENNReal.ofReal ((15 / 16 : Real) ^ (4 * n)) ≤
      worstProbability separationPi (1 / 2 : Real) 1 (retrySurvivalEvent M B (8 * n)) ∧
    worstProbability separationPi (1 / 2 : Real) 1 (retrySurvivalEvent M B (8 * n)) ≤
      ENNReal.ofReal ((9 / 8 : Real) * (225 / 256 : Real) ^ n) ∧
    (9 / 8 : Real) * (225 / 256 : Real) ^ n < 1 ∧
    (∃ nu : Measure (Nat -> Bool), nu ∈ SourceClass separationPi (1 / 2 : Real) 1 ∧
      nu (retrySurvivalEvent M A (8 * n)) = 1 ∧
      nu (retrySurvivalEvent M B (8 * n)) ≤
        ENNReal.ofReal ((9 / 8 : Real) * (225 / 256 : Real) ^ n)) ∧
    (∀ sel, IsValidRetrySelector sel ->
      ENNReal.ofReal ((15 / 16 : Real) ^ (4 * n)) ≤
        worstProbability separationPi (1 / 2 : Real) 1 (retrySurvivalEvent M sel (8 * n))) ∧
    (∀ T sel, IsValidRetrySelector sel ->
      worstProbability separationPi (1 / 2 : Real) 1 (retrySurvivalEvent M B T) ≤
        worstProbability separationPi (1 / 2 : Real) 1 (retrySurvivalEvent M sel T)) ∧
    ∀ sel1 sel2, IsValidRetrySelector sel1 -> IsValidRetrySelector sel2 ->
      ∀ T, retryReferenceTail M sel1 separationPi T = retryReferenceTail M sel2 separationPi T ∧
        ∀ theta, 0 < theta ->
          retryCompletionPrefixPowerSum M sel1 separationPi T theta =
              retryCompletionPrefixPowerSum M sel2 separationPi T theta ∧
            retryPrefixPowerSum M sel1 separationPi T theta =
              retryPrefixPowerSum M sel2 separationPi T theta := by sorry

end CorrelatedLocalSearch.Supplement
