-- Prove2me | Theorems.Thm_CountingLLL_ContractedWalk_generating_function_integral
-- name    : CountingLLL.ContractedWalk.generating_function_integral
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:31:29.68365+00:00
-- url     : https://prove2.me/theorems/3687bed3-fb84-4ec3-ad0d-84d6211f3025
-- title:
--   Integral of the contracted walk generating function
-- statement:
--   For $0\le\theta<1/3$, the integral from zero to one of the upward-count generating function of the contracted walk equals $1-\theta/(2(1-\theta))$. This is the exact integral identity used in the proof of Lemma 6.5.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 #442, proof of Lemma 6.5, PDF p. 27, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ContractedGF
open MeasureTheory CountingLLL.ContractedWalk

theorem CountingLLL.ContractedWalk.generating_function_integral (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ < 1/3) :
    (∫ z in (0:ℝ)..1, generatingFunction θ z) = 1-θ/(2*(1-θ)) := by sorry
