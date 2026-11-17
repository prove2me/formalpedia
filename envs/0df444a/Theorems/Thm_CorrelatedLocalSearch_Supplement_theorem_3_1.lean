-- Prove2me | Theorems.Thm_CorrelatedLocalSearch_Supplement_theorem_3_1
-- name    : CorrelatedLocalSearch.Supplement.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:04:37.917881+00:00
-- url     : https://prove2.me/theorems/eda28fab-8932-42c6-9823-f73cfddaddbf
-- title:
--   Theorem 3.1 — optimal retry priority under a prefix probability bound
-- statement:
--   For $0<s\le1$, always attempting an unfinished task with smallest $w_i=\sum_{a\in B_i}\pi(a)^s$ minimizes the worst probability of $\{\tau>T\}$ simultaneously for every $T$ and $D\ge1$. For sorted weights, the displayed recursion has exact optimum $\min\{1,Dv_T(1)\}$ and uses $O(nT)$ arithmetic and $O(n)$ memory. Every valid selector has the same stopping-time law under $P$ and the same two powered prefix sums $Z_T$ and $\widetilde Z_T$ at every depth and exponent.
--
--   Differences from the source:
--   - encoding: arithmetic-operation and memory bounds in big-O notation → the explicit in-place row evaluation of the displayed recurrence uses at most $4nT$ arithmetic operations and $n+1$ cells; reason: an explicit costed evaluation witnesses the stated asymptotics
--   - encoding: worst probabilities written as nonnegative real quantities → `ENNReal`; reason: exact nonnegative encoding
-- source:
--   Xu, Local Search with Correlated Randomness, arXiv:2607.17469 (sha256 17e00d69…), Theorem 3.1, p.7 (PDF p.9)

import Mathlib
import Definitions.Def_CorrelatedLocalSearch_Supplement_RetryTasks

set_option autoImplicit false

namespace CorrelatedLocalSearch.Supplement

open MeasureTheory
open scoped ENNReal BigOperators

/-- Xu, arXiv:2607.17469 (sha256 17e00d69…), Theorem 3.1, p.7 (PDF p.9).
The smallest powered success-set weight first is simultaneously minimax at every deadline and
slack; the displayed suffix recursion is exact; its arithmetic cost is linear in `nT`; and every
selector has the same independent stopping law and every powered single-depth sum. -/
theorem theorem_3_1 {A : Type*} [Fintype A] [DecidableEq A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (hA : 2 ≤ Fintype.card A) (pi : A -> Real) (hpi : ∀ a, 0 < pi a)
    (hpisum : (∑ a, pi a) = 1) (n : Nat) (hn : 1 ≤ n)
    (M : RetryModel A (Fin n)) (s : Real) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (order : List (Fin n)) (horder : order.Nodup)
    (hcomplete : ∀ i, i ∈ order)
    (hsorted : order.Pairwise (fun i j => taskPowerWeight M pi s i ≤ taskPowerWeight M pi s j)) :
    ∃ priority : RetrySelector A (Fin n),
      IsValidRetrySelector priority ∧ AlwaysChoosesSmallest M pi s priority ∧
      (∀ D, 1 ≤ D -> ∀ T,
        worstProbability pi s D (retrySurvivalEvent M priority T) =
          min 1 (ENNReal.ofReal D * ENNReal.ofReal
            (retryValue (totalPowerWeight pi s)
              (order.map (taskPowerWeight M pi s)) T 0)) ∧
        (∃ nu : Measure (Nat -> A), nu ∈ SourceClass pi s D ∧
          nu (retrySurvivalEvent M priority T) =
            worstProbability pi s D (retrySurvivalEvent M priority T)) ∧
        ∀ sel, IsValidRetrySelector sel ->
          worstProbability pi s D (retrySurvivalEvent M priority T) ≤
            worstProbability pi s D (retrySurvivalEvent M sel T)) ∧
      (∀ T, (retryValueTable (totalPowerWeight pi s)
          (order.map (taskPowerWeight M pi s)) T).getD 0 0 =
            retryValue (totalPowerWeight pi s)
              (order.map (taskPowerWeight M pi s)) T 0 ∧
        retryArithmeticOperations n T ≤ 4 * n * T) ∧
      retryMemoryCells n ≤ n + 1 ∧
      ∀ sel1 sel2, IsValidRetrySelector sel1 -> IsValidRetrySelector sel2 ->
        ∀ T, retryReferenceTail M sel1 pi T = retryReferenceTail M sel2 pi T ∧
          ∀ theta, 0 < theta ->
            retryCompletionPrefixPowerSum M sel1 pi T theta =
                retryCompletionPrefixPowerSum M sel2 pi T theta ∧
              retryPrefixPowerSum M sel1 pi T theta =
                retryPrefixPowerSum M sel2 pi T theta := by sorry

end CorrelatedLocalSearch.Supplement
