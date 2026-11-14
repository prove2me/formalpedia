-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_full_suppressed_ignores_return_entropy
-- name    : CountingLLL.ReciprocalTest.full_suppressed_ignores_return_entropy
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:47:29.152579+00:00
-- url     : https://prove2.me/theorems/158d902b-5e9f-4b0c-9fb6-a5a0de6920a7
-- title:
--   Fully suppressed execution ignores the initial return bit and uniform returns
-- statement:
--   The entire fully suppressed ReciprocalTest state trajectory is unchanged if its initial fair bit and all uniform-return draws are altered while every oracle answer and every later fair bit are held fixed. In particular, those ignored entropy coordinates can be treated independently of the suppressed trajectory under the product law. This statement is pathwise; it does not assert independence of the later counter-dependent fair-bit check.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovász Local Lemma, STOC submission #442, §6.2, Lemma 6.5; suppressed-return coupling.

import Definitions.Def_CountingLLL_ReciprocalAllSuppressed
open CountingLLL.ReciprocalTest

theorem CountingLLL.ReciprocalTest.full_suppressed_ignores_return_entropy (ω ω' : Entropy)
    (ho : ω.1 = ω'.1) (hf : ∀ k ≥ 1, ω.2.1 k = ω'.2.1 k) (n : ℕ) :
    allSuppressedRun ω n = allSuppressedRun ω' n := by sorry
