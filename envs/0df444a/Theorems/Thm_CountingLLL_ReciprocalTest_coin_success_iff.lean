-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_coin_success_iff
-- name    : CountingLLL.ReciprocalTest.coin_success_iff
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:57:43.902511+00:00
-- url     : https://prove2.me/theorems/28b53e9b-afcb-49bd-9a64-6b6bd6dd7697
-- title:
--   Coin first-exit event equals its operational success event
-- statement:
--   Start the initial Coin call in Algorithm 6 with fresh oracle and fair-bit streams. It returns one exactly when, for some $n$, the first $n$ oracle and corresponding fair bits are all zero and the next oracle answer is one. This identifies the IID first-exit event with the operational small-step execution, path by path, without assuming termination.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 #442, Algorithm 6 lines 1–7, PDF p. 27, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ReciprocalTest
open CountingLLL.ReciprocalTest

theorem CountingLLL.ReciprocalTest.coin_success_iff (ω : Entropy) : (∃ t, ((step ω)^[t] ({phase := .coinOracle .initial} : State)).phase = .initialCheck) ↔ ∃ n, (∀ k < n, ω.1 k = false ∧ ω.2.1 k = false) ∧ ω.1 n = true := by sorry
