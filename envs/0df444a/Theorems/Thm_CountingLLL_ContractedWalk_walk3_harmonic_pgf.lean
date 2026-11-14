-- Prove2me | Theorems.Thm_CountingLLL_ContractedWalk_walk3_harmonic_pgf
-- name    : CountingLLL.ContractedWalk.walk3_harmonic_pgf
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:06:55.815899+00:00
-- url     : https://prove2.me/theorems/bdec1ee1-50b7-4254-ac05-b7f2db566814
-- title:
--   Contracted-walk harmonic expectation and generating function
-- statement:
--   For $0\le\theta<1/3$, let $U_3$ be the upward-change count of the paper’s contracted walk started from level three, and let $G$ be the corresponding generating function from level one. Then $$\mathbb E\!\left[\sum_{k=0}^{U_3-1}\frac1{k+2}\right]=\int_0^1\frac{z(1-G(z)^3)}{1-z}\,dz.$$
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, proof of Lemma 6.5, calls to O, p. 28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ContractedGF
open MeasureTheory CountingLLL.ContractedWalk
open scoped ENNReal Interval BigOperators

theorem CountingLLL.ContractedWalk.walk3_harmonic_pgf (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ < 1/3) :
    (∫ ω : Tape, ∑ k ∈ Finset.range (upwardCount ω 3), (1:ℝ)/(k+2) ∂tapeLaw (ENNReal.ofReal θ)) =
      ∫ z in (0:ℝ)..1, z*(1-(generatingFunction θ z)^3)/(1-z) := by sorry
