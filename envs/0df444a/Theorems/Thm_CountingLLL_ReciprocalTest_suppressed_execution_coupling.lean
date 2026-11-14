-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_suppressed_execution_coupling
-- name    : CountingLLL.ReciprocalTest.suppressed_execution_coupling
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:40:55.588655+00:00
-- url     : https://prove2.me/theorems/84ae897a-1142-4c18-91b3-5ae62497bf8d
-- title:
--   Pathwise coupling of ReciprocalTest with its suppressed-return execution
-- statement:
--   Couple the operational algorithm and the execution in which its initial counter-dependent and later uniform return checks are suppressed, using the same entropy tape. At each time they are equal or the original has already returned true. If all suppressed checks through a given time are survived, their states are equal; if the next check fails while they are synchronized, the original immediately returns true. The suppressed execution is unchanged when the uniform-check entropy is replaced while keeping the oracle and fair-bit arrays fixed.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovász Local Lemma, STOC submission #442, §6.2, Lemma 6.5. This establishes the pathwise suppressed-check coupling used toward, but does not itself establish, the paper’s output and cost bounds.

import Definitions.Def_CountingLLL_ReciprocalSuppressed
open CountingLLL.ReciprocalTest

theorem CountingLLL.ReciprocalTest.suppressed_execution_coupling :
    (∀ ω : Entropy, ∀ n : ℕ, run ω n = suppressedRun ω n ∨ (run ω n).phase = .done true) ∧
    (∀ (ω : Entropy) (n : ℕ),
      (∀ t < n, ((suppressedRun ω t).phase = .initialCheck → ω.2.1 (suppressedRun ω t).fairUsed = false) ∧
        ((suppressedRun ω t).phase = .uniformCheck → (ω.2.2 ((suppressedRun ω t).j-1,(suppressedRun ω t).uniformUsed)).val ≠ 0)) →
      run ω n = suppressedRun ω n) ∧
    (∀ (ω : Entropy) (n : ℕ), run ω n = suppressedRun ω n →
      (((suppressedRun ω n).phase = .initialCheck ∧ ω.2.1 (suppressedRun ω n).fairUsed = true) ∨
       ((suppressedRun ω n).phase = .uniformCheck ∧ (ω.2.2 ((suppressedRun ω n).j-1,(suppressedRun ω n).uniformUsed)).val = 0)) →
      (run ω (n+1)).phase = .done true) ∧
    (∀ (ω ω' : Entropy), ω.1 = ω'.1 → ω.2.1 = ω'.2.1 → ∀ n : ℕ,
      suppressedRun ω n = suppressedRun ω' n) := by sorry
