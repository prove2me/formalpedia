-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_oracle_progress
-- name    : CountingLLL.ReciprocalTest.oracle_progress
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:24:08.458994+00:00
-- url     : https://prove2.me/theorems/9a06c526-fb6b-4c59-ab96-7f0ced6ab1b3
-- title:
--   Live ReciprocalTest execution makes oracle-call progress
-- statement:
--   At every finite time $n$ when the operational ReciprocalTest has not halted, its oracle-call counter is at least $(n-1)/4$. Equivalently, $n\le4\,\text{oracleUsed}+1$. This pathwise progress bound implies that any nonhalting execution makes infinitely many oracle calls.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, Algorithm 6, pp. 27–28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ReciprocalTest
open CountingLLL.ReciprocalTest

theorem CountingLLL.ReciprocalTest.oracle_progress (ω : Entropy) (n : ℕ)
    (hlive : (run ω n).phase ≠ .done false ∧ (run ω n).phase ≠ .done true) :
    n ≤ 4*(run ω n).oracleUsed+1 := by sorry
