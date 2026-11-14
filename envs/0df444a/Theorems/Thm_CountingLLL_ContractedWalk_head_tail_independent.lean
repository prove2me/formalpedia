-- Prove2me | Theorems.Thm_CountingLLL_ContractedWalk_head_tail_independent
-- name    : CountingLLL.ContractedWalk.head_tail_independent
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:36:34.985639+00:00
-- url     : https://prove2.me/theorems/a3c2edd9-fe32-4047-af1b-e813fb496200
-- title:
--   First increment is independent of the remaining tape
-- statement:
--   For the IID contracted-walk increment stream, its first bit is independent of the entire shifted tail. This supplies the independence required to take expectations in the first-step recursion.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 #442, proof of Lemma 6.5, PDF p. 27, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ContractedWalk
open MeasureTheory ProbabilityTheory CountingLLL.ContractedWalk
open scoped ENNReal

theorem CountingLLL.ContractedWalk.head_tail_independent (p : ℝ≥0∞) (hp : p ≤ 1) : IndepFun (fun ω : Tape => ω 0) (fun ω : Tape => fun n => ω (n+1)) (tapeLaw p) := by sorry
