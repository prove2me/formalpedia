-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_full_suppressed_coupling
-- name    : CountingLLL.ReciprocalTest.full_suppressed_coupling
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:45:19.900581+00:00
-- url     : https://prove2.me/theorems/96bb9e92-53e0-485e-9e4d-92238e3acd03
-- title:
--   Fully suppressed ReciprocalTest coupling and false-output characterization
-- statement:
--   Couple the operational ReciprocalTest program to the auxiliary execution in which all early returns are suppressed, using the same entropy arrays. At every finite time, either their states coincide or the original has already returned true. The original returns false if and only if the fully suppressed execution reaches false absorption and every earlier fair-bit or uniform return check survives. This is a pathwise equivalence for every entropy tape, including nonterminating tapes.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovász Local Lemma, STOC submission #442, §6.2, Lemma 6.5, PDF pp. 27–28. This establishes the pathwise part of the paper’s suppressed-return argument, not the probability or cost bound.

import Definitions.Def_CountingLLL_ReciprocalAllSuppressed
open CountingLLL.ReciprocalTest

theorem CountingLLL.ReciprocalTest.full_suppressed_coupling (ω : Entropy) :
    (∀ n : ℕ, run ω n = allSuppressedRun ω n ∨ (run ω n).phase = .done true) ∧
    (Returns ω false ↔ ∃ n : ℕ, (allSuppressedRun ω n).phase = .done false ∧
      ∀ t < n, (((allSuppressedRun ω t).phase = .start ∨ (allSuppressedRun ω t).phase = .initialCheck) → ω.2.1 (allSuppressedRun ω t).fairUsed = false) ∧
        ((allSuppressedRun ω t).phase = .uniformCheck → (ω.2.2 ((allSuppressedRun ω t).j-1,(allSuppressedRun ω t).uniformUsed)).val ≠ 0)) := by sorry
