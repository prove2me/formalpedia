-- Prove2me | Theorems.Thm_CountingLLL_ContractedWalk_generating_function_bounds
-- name    : CountingLLL.ContractedWalk.generating_function_bounds
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:41:39.78592+00:00
-- url     : https://prove2.me/theorems/22cea12c-1541-4bce-b7ea-0779648b7000
-- title:
--   Contracted-walk generating function lies in [0,1]
-- statement:
--   For a valid contracted-walk tape law and $0\le z\le1$, the stopped upward-count probability generating function lies between zero and one. These bounds are needed when selecting the relevant solution of the paper’s cubic recursion.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 #442, proof of Lemma 6.5, PDF p. 27, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ContractedGF
open MeasureTheory CountingLLL.ContractedWalk

theorem CountingLLL.ContractedWalk.generating_function_bounds (θ z : ℝ) (hθ : θ ≤ 1) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : 0 ≤ generatingFunction θ z ∧ generatingFunction θ z ≤ 1 := by sorry
