-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_false_output_iff_suppressed_survival
-- name    : CountingLLL.ReciprocalTest.false_output_iff_suppressed_survival
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:42:14.326925+00:00
-- url     : https://prove2.me/theorems/20dae367-0bf2-4821-8609-2f86a93fd192
-- title:
--   False output equals suppressed absorption with all checks survived
-- statement:
--   The operational ReciprocalTest algorithm returns false exactly when its coupled suppressed-return execution reaches false absorption and every initial or uniform return check before that time is survived. This is a pathwise identity valid for every entropy tape, without a termination or probability assumption.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovász Local Lemma, STOC submission #442, §6.2, Lemma 6.5; pathwise coupling underlying the product of return-check survival probabilities.

import Definitions.Def_CountingLLL_ReciprocalSuppressed
open CountingLLL.ReciprocalTest

theorem CountingLLL.ReciprocalTest.false_output_iff_suppressed_survival (ω : Entropy) :
    Returns ω false ↔ ∃ n : ℕ, (suppressedRun ω n).phase = .done false ∧
      ∀ t < n, ((suppressedRun ω t).phase = .initialCheck → ω.2.1 (suppressedRun ω t).fairUsed = false) ∧
        ((suppressedRun ω t).phase = .uniformCheck → (ω.2.2 ((suppressedRun ω t).j-1,(suppressedRun ω t).uniformUsed)).val ≠ 0) := by sorry
