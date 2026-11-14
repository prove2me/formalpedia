-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_coin_first_return_and_cost
-- name    : CountingLLL.ReciprocalTest.coin_first_return_and_cost
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:21:55.13304+00:00
-- url     : https://prove2.me/theorems/bf84d434-b26b-483b-bd5f-bd073028fcfe
-- title:
--   Operational Coin first return and exact oracle count
-- statement:
--   Start the operational local Coin procedure with unused entropy streams. Suppose the first $n$ oracle and fair-bit pairs are both false, and in the next pair at least one bit is true. Then Coin first returns after exactly $n+1$ oracle calls: there is a return state with that call count, and no earlier step is a return state. This pathwise result connects the geometric-trial description to the small-step machine.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, Algorithm 6 and proof of Lemma 6.5, pp. 27–28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ReciprocalTest
open CountingLLL.ReciprocalTest

theorem CountingLLL.ReciprocalTest.coin_first_return_and_cost (ω : Entropy) (n : ℕ)
    (h : ∀ k < n, ω.1 k = false ∧ ω.2.1 k = false)
    (hexit : ω.1 n = true ∨ ω.2.1 n = true) :
    ∃ T, (((step ω)^[T] ({phase := .coinOracle .initial} : State)).phase = .initialCheck ∨
           ((step ω)^[T] ({phase := .coinOracle .initial} : State)).phase = .loop) ∧
      ((step ω)^[T] ({phase := .coinOracle .initial} : State)).oracleUsed = n+1 ∧
      ∀ t < T, ((step ω)^[t] ({phase := .coinOracle .initial} : State)).phase ≠ .initialCheck ∧
        ((step ω)^[t] ({phase := .coinOracle .initial} : State)).phase ≠ .loop := by sorry
