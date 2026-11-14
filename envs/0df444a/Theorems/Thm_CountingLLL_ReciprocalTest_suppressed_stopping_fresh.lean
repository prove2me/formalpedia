-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_suppressed_stopping_fresh
-- name    : CountingLLL.ReciprocalTest.suppressed_stopping_fresh
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T11:09:26.339204+00:00
-- url     : https://prove2.me/theorems/4036f844-f683-49cb-9c97-03124f2bc4e2
-- title:
--   Fresh entropy at history-adapted stopping times
-- statement:
--   Let an optional stopping time for the fully suppressed ReciprocalTest be determined, at each finite time, by the execution history up to that time. Conditional in joint-probability form on its being finite and on a given current query state, the next queried entropy coordinate has its original marginal law. The stopping time may be infinite; the result does not assume almost-sure termination.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovász Local Lemma, STOC submission #442, §6.2, Lemma 6.5; stopping-time fresh-input tool for the adaptive contracted walk.

import Definitions.Def_CountingLLL_ReciprocalEncodedLaw
import Definitions.Def_CountingLLL_ReciprocalAllSuppressed
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest
open scoped ENNReal

theorem CountingLLL.ReciprocalTest.suppressed_stopping_fresh (B : ℝ≥0∞) (hB : B ≤ 1) (T : Entropy → Option ℕ)
    (H : (n : ℕ) → (Fin (n+1) → State) → Prop)
    (hT : ∀ ω n, T ω = some n ↔ H n (fun j => allSuppressedRun ω j.val))
    (s : State) (a : ReadIndex) (ha : readIndex s = some a) (U : Set ℕ) :
    entropyLaw B {ω | ∃ n, T ω = some n ∧ allSuppressedRun ω n = s ∧ entropyCode ω a ∈ U} =
      entropyLaw B {ω | ∃ n, T ω = some n ∧ allSuppressedRun ω n = s} * readLaw B a U := by sorry
