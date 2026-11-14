-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_full_suppressed_epoch_coupling
-- name    : CountingLLL.ReciprocalTest.full_suppressed_epoch_coupling
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:52:47.008329+00:00
-- url     : https://prove2.me/theorems/e48e811d-2f88-40cc-891f-ce51d605c793
-- title:
--   Pathwise coupling of actual counter-change epochs to the contracted walk
-- statement:
--   Start the fully suppressed operational execution in a main-walk phase and erase the steps that do not change its first counter. Assume explicitly that whenever the counter at a change epoch is nonzero, a later change exists. Then, pathwise for every change index, the first counter equals the paper’s abstract contracted walk driven by the extracted actual up/down directions, and the second counter equals its initial value plus the number of upward directions. The theorem makes no assertion that the extracted directions are independent or that the nonsticking hypothesis holds almost surely.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovász Local Lemma, STOC submission #442, §6.2, Lemma 6.5, PDF p. 28. This is the deterministic part of the suppressed-run contracted-walk coupling.

import Definitions.Def_CountingLLL_ReciprocalWalkEpoch
open CountingLLL.ReciprocalTest

theorem CountingLLL.ReciprocalTest.full_suppressed_epoch_coupling (ω : Entropy) (start : ℕ)
    (hphase : (match (allSuppressedRun ω start).phase with
      | .loop | .coinOracle .first | .coinFair .first | .coinOracle .second | .coinFair .second
      | .uniformCheck | .done _ => True | _ => False))
    (hprogress : ∀ n, (allSuppressedRun ω (changeEpoch ω start n)).i ≠ 0 →
      ∃ k, changeEpoch ω start n < k ∧
        (allSuppressedRun ω k).i ≠ (allSuppressedRun ω (changeEpoch ω start n)).i) :
    ∀ n, (allSuppressedRun ω (changeEpoch ω start n)).i =
      CountingLLL.ContractedWalk.level (changeDirection ω start) (allSuppressedRun ω start).i n ∧
      (allSuppressedRun ω (changeEpoch ω start n)).j =
        (allSuppressedRun ω start).j + ∑ t ∈ Finset.range n, (if changeDirection ω start t then 1 else 0 : ℕ) := by sorry
