-- Prove2me | Theorems.Thm_CountingLLL_ContractedWalk_abstract_counter_output_formula
-- name    : CountingLLL.ContractedWalk.abstract_counter_output_formula
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:23:59.289096+00:00
-- url     : https://prove2.me/theorems/bb3c8f9a-cd03-4ba0-8eba-257cbf2b43bc
-- title:
--   Abstract contracted-counter reciprocal output formula
-- statement:
--   For $e^{-3/10}\le B<1$, let $u=2(1-B)/(2-B)$ and $\theta=u^2/(1-u+u^2)$. Draw an independent Bernoulli-$u$ initial bit, then run the absorbed contracted walk from level one or three as dictated by that bit. If $N$ is the corresponding final counter, then $1-\frac12\mathbb E[1/N]=1/(2B)$. This proves the output calculation in the abstract suppressed-return counter model; the pathwise connection to the complete ReciprocalTest is a separate result.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 #442, proof of Lemma 6.5, PDF pp. 27–28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ContractedGF
open MeasureTheory CountingLLL.ContractedWalk
open scoped ENNReal Interval

theorem CountingLLL.ContractedWalk.abstract_counter_output_formula (B : ℝ) (hB0 : 0 < B) (hB1 : B < 1) (hB : Real.exp (-(3/10 : ℝ)) ≤ B) :
    let u := 2*(1-B)/(2-B)
    let θ := u^2/(1-u+u^2)
    let ν := (bitLaw (ENNReal.ofReal u)).prod (tapeLaw (ENNReal.ofReal θ))
    1-(∫ x : Bool × Tape, (1:ℝ)/(((if x.1 then 1 + upwardCount x.2 3 else upwardCount x.2 1) : ℕ) + 1 : ℝ) ∂ν)/2 = 1/(2*B) := by sorry
