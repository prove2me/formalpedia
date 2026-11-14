-- Prove2me | Theorems.Thm_CountingLLL_ContractedWalk_generating_function_factor
-- name    : CountingLLL.ContractedWalk.generating_function_factor
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:02:18.149534+00:00
-- url     : https://prove2.me/theorems/9b9f38d2-e69a-4e05-8e31-9097d2e5fca3
-- title:
--   First-hit factorization of contracted-walk generating functions
-- statement:
--   For $0\le\theta<1/3$ and $0\le z\le1$, let $F_m(z)$ be the generating function of upward moves before the contracted walk from level $m$ reaches zero. Then $F_{m+1}(z)=F_1(z)F_m(z)$. This is the independent first-hit segmentation used in the paper to obtain the cubic recursion.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 #442, proof of Lemma 6.5, PDF p. 27, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ContractedGF
open MeasureTheory CountingLLL.ContractedWalk

theorem CountingLLL.ContractedWalk.generating_function_factor (θ z : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ < 1/3)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (m : ℕ) :
    (∫ ω : Tape, z ^ upwardCount ω (m+1) ∂tapeLaw (ENNReal.ofReal θ)) =
      (∫ ω : Tape, z ^ upwardCount ω 1 ∂tapeLaw (ENNReal.ofReal θ)) *
      (∫ ω : Tape, z ^ upwardCount ω m ∂tapeLaw (ENNReal.ofReal θ)) := by sorry
