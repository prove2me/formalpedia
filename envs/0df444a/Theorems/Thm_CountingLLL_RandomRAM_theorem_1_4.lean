-- Prove2me | Theorems.Thm_CountingLLL_RandomRAM_theorem_1_4
-- name    : CountingLLL.RandomRAM.theorem_1_4
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T04:59:10.216197+00:00
-- url     : https://prove2.me/theorems/e818d217-d687-45f3-80c8-86d598a9f4ab
-- title:
--   Near-linear expected-time exact sampling under the counting and sampling LLL
-- statement:
--   There is a fixed fair-bit oracle RAM program and universal constants such that, on every instance satisfying the standing hypotheses and Condition 1.1, the program terminates almost surely and outputs each satisfying assignment with probability exactly 1/Z, while all nonsatisfying assignments have probability zero. Its expected evaluation-oracle cost is O(m), and expected bit time is at most a universal constant times (n+k m D^2) times a polylogarithmic factor in m, n, and q. The machine uses the explicit input and output encodings specified in the imported definitions. This is an open formal target, not a verified implementation.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovasz Local Lemma, STOC 2027 submission #442, Theorems 1.3 and 1.4, PDF page 4, and computational model in Section 2.5, PDF page 8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_RandomSpec

theorem CountingLLL.RandomRAM.theorem_1_4 : ∃ (P : CountingLLL.RandomRAM.Program) (C r : ℕ), CountingLLL.RandomRAM.IsExactSampler P C r := by sorry
