-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_shifted_coin_exit
-- name    : CountingLLL.ReciprocalTest.shifted_coin_exit
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:31:08.133197+00:00
-- url     : https://prove2.me/theorems/203ee8c6-7047-4dca-b670-5def3d618600
-- title:
--   Coin trace at arbitrary entropy offsets and call sites
-- statement:
--   Consider any machine state and any of the three call-site contexts of Algorithm 6. If the next $n$ oracle and fair-bit pairs at the state’s current offsets are both false, then the first nonfailed pair returns through the appropriate continuation. The theorem gives the exact small-step state and consumed entropy counters for either an oracle-success exit or a fair-bit exit.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, Algorithm 6, pp. 27–28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ReciprocalTest
open CountingLLL.ReciprocalTest

theorem CountingLLL.ReciprocalTest.shifted_coin_exit (ω : Entropy) (s : State) (ctx : Context) (n : ℕ)
    (h : ∀ k < n, ω.1 (s.oracleUsed+k) = false ∧ ω.2.1 (s.fairUsed+k) = false) :
    (ω.1 (s.oracleUsed+n) = true →
      (step ω)^[2*n+1] ({s with phase := .coinOracle ctx} : State) =
        coinReturn ctx true {s with phase := .coinOracle ctx, oracleUsed := s.oracleUsed+n+1, fairUsed := s.fairUsed+n}) ∧
    (ω.1 (s.oracleUsed+n) = false → ω.2.1 (s.fairUsed+n) = true →
      (step ω)^[2*n+2] ({s with phase := .coinOracle ctx} : State) =
        coinReturn ctx false {s with phase := .coinOracle ctx, oracleUsed := s.oracleUsed+n+1, fairUsed := s.fairUsed+n+1}) := by sorry
