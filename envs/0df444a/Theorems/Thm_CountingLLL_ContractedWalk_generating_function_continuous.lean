-- Prove2me | Theorems.Thm_CountingLLL_ContractedWalk_generating_function_continuous
-- name    : CountingLLL.ContractedWalk.generating_function_continuous
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:12:37.121484+00:00
-- url     : https://prove2.me/theorems/391a53fa-6d78-4344-8b0a-9c5003c74006
-- title:
--   Continuity of the contracted-walk generating function
-- statement:
--   For $0\le\theta<1/3$, the stopped upward-count generating function is continuous on $[0,1]$. This supplies the regularity needed for the source’s generating-function change of variables.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 #442, proof of Lemma 6.5, PDF p. 27, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ContractedGF
open CountingLLL.ContractedWalk

theorem CountingLLL.ContractedWalk.generating_function_continuous (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ < 1/3) : ContinuousOn (generatingFunction θ) (Set.Icc (0:ℝ) 1) := by sorry
