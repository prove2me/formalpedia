-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_coin_success_path
-- name    : CountingLLL.ReciprocalTest.coin_success_path
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:56:03.106197+00:00
-- url     : https://prove2.me/theorems/8e4413b7-4aec-46d8-a512-aeb4a7b8b05b
-- title:
--   Coin success path in the small-step machine
-- statement:
--   Start Algorithm 6’s initial Coin call with fresh random streams. If the first $n$ oracle answers and corresponding fair bits are zero and the next oracle answer is one, then after exactly $2n+1$ atomic machine steps the call has returned one and the machine reaches its initial-return check. This establishes one direction of the pathwise bridge between the IID first-exit calculation and the operational model.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 #442, Algorithm 6 lines 1–7, PDF p. 27, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ReciprocalTest
open CountingLLL.ReciprocalTest

theorem CountingLLL.ReciprocalTest.coin_success_path (ω : Entropy) (n : ℕ) (h : ∀ k < n, ω.1 k = false ∧ ω.2.1 k = false) (ho : ω.1 n = true) : ((step ω)^[2*n+1] ({phase := .coinOracle .initial} : State)).phase = .initialCheck := by sorry
