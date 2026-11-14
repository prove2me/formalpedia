-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_uniform_size_positive
-- name    : CountingLLL.ReciprocalTest.uniform_size_positive
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:41:48.79918+00:00
-- url     : https://prove2.me/theorems/fbb77712-8c52-4d79-8621-776700a1d04e
-- title:
--   ReciprocalTest uses positive uniform ranges
-- statement:
--   For every entropy realization and every execution step of Algorithm 6, when the algorithm requests a uniform draw on $\{1,\ldots,j\}$, its counter satisfies $j>0$. Consequently, the finite distribution used by the operational model has exactly the intended $j$ outcomes.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 #442, Algorithm 6, line 14, PDF p. 27, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ReciprocalTest
open CountingLLL.ReciprocalTest

theorem CountingLLL.ReciprocalTest.uniform_size_positive (ω : Entropy) (n : ℕ) (h : (run ω n).phase = .uniformCheck) : 0 < (run ω n).j := by sorry
