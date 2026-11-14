-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_full_suppressed_first_change
-- name    : CountingLLL.ReciprocalTest.full_suppressed_first_change
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:49:18.005281+00:00
-- url     : https://prove2.me/theorems/4ade3308-38d2-4d91-9940-747b3093f123
-- title:
--   First nontrivial counter change after contracting self-loops
-- statement:
--   Suppose the fully suppressed execution is in the main walk at time m, its first counter stays constant until a later time n, and at n that counter changes. Then the intervening self-loops also leave the second counter fixed, and the change is exactly either a decrease of the first counter by one or an increase of the two counters by two and one. The resulting phase remains a main-walk phase. This is the pathwise contraction step and does not assert transition probabilities.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovász Local Lemma, STOC submission #442, §6.2, Lemma 6.5, PDF p. 28; contraction of iterations leaving the two counters unchanged.

import Definitions.Def_CountingLLL_ReciprocalAllSuppressed
open CountingLLL.ReciprocalTest

theorem CountingLLL.ReciprocalTest.full_suppressed_first_change (ω : Entropy) (m n : ℕ) (hmn : m < n)
    (hphase : (match (allSuppressedRun ω m).phase with
    | .loop | .coinOracle .first | .coinFair .first | .coinOracle .second | .coinFair .second
    | .uniformCheck | .done _ => True | _ => False))
    (hconstant : ∀ t, m < t → t < n → (allSuppressedRun ω t).i = (allSuppressedRun ω m).i)
    (hchange : (allSuppressedRun ω n).i ≠ (allSuppressedRun ω m).i) :
    (((allSuppressedRun ω n).i = (allSuppressedRun ω m).i - 1 ∧
       (allSuppressedRun ω n).j = (allSuppressedRun ω m).j) ∨
     ((allSuppressedRun ω n).i = (allSuppressedRun ω m).i + 2 ∧
       (allSuppressedRun ω n).j = (allSuppressedRun ω m).j + 1)) ∧
    (match (allSuppressedRun ω n).phase with
    | .loop | .coinOracle .first | .coinFair .first | .coinOracle .second | .coinFair .second
    | .uniformCheck | .done _ => True | _ => False) := by sorry
