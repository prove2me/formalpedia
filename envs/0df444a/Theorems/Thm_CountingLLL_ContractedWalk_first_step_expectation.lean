-- Prove2me | Theorems.Thm_CountingLLL_ContractedWalk_first_step_expectation
-- name    : CountingLLL.ContractedWalk.first_step_expectation
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:45:59.707289+00:00
-- url     : https://prove2.me/theorems/2485d64f-d13a-4588-9201-1c66dcde1c12
-- title:
--   Contracted-walk generating functions satisfy first-step recurrence
-- statement:
--   Let $F_i(z)$ be the generating function of the number of upward moves before the contracted walk from level $i$ hits zero. For $i>0$, $0\le\theta<1/3$ and $0\le z\le1$, the first-step recurrence is $F_i(z)=(1-\theta)F_{i-1}(z)+\theta zF_{i+2}(z)$. This establishes the first-step part of the paper’s generating-function analysis.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 #442, proof of Lemma 6.5, PDF p. 27, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ContractedGF
open MeasureTheory CountingLLL.ContractedWalk

theorem CountingLLL.ContractedWalk.first_step_expectation (θ z : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ < 1/3)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (i : ℕ) (hi : 0 < i) :
    (∫ ω : Tape, z ^ upwardCount ω i ∂tapeLaw (ENNReal.ofReal θ)) =
      (1-θ)*(∫ ω : Tape, z ^ upwardCount ω (i-1) ∂tapeLaw (ENNReal.ofReal θ)) +
      θ*z*(∫ ω : Tape, z ^ upwardCount ω (i+2) ∂tapeLaw (ENNReal.ofReal θ)) := by sorry
