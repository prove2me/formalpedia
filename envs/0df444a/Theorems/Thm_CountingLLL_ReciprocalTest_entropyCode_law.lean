-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_entropyCode_law
-- name    : CountingLLL.ReciprocalTest.entropyCode_law
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:05:05.464295+00:00
-- url     : https://prove2.me/theorems/15b8859d-7ff2-4851-8014-d4af6a19e418
-- title:
--   Encoded reveal input has the original entropy law
-- statement:
--   For $B\le1$, encoding the original independent oracle, fair-bit, and finite-uniform entropy streams as a single tagged natural-valued array gives exactly the independent encoded input law. Thus the reveal-machine input representation preserves the original joint distribution.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, Algorithm 6, pp. 27–28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ReciprocalEncodedLaw
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest
open scoped ENNReal

theorem CountingLLL.ReciprocalTest.entropyCode_law (B : ℝ≥0∞) (hB : B ≤ 1) :
    (entropyLaw B).map entropyCode = encodedEntropyLaw B := by sorry
