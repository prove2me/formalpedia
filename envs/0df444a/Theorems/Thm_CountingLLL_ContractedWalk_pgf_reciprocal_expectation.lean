-- Prove2me | Theorems.Thm_CountingLLL_ContractedWalk_pgf_reciprocal_expectation
-- name    : CountingLLL.ContractedWalk.pgf_reciprocal_expectation
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:21:30.705212+00:00
-- url     : https://prove2.me/theorems/1197cc0a-f91d-4b2d-8176-900ed3607fbd
-- title:
--   Integral of a probability generating function equals a reciprocal expectation
-- statement:
--   If $K$ is a measurable nonnegative integer-valued random variable on a probability space, then $\mathbb E[1/(K+1)]=\int_0^1\mathbb E[z^K]\,dz$. The bounded-integrand interchange rigorously connects the paper’s counter generating function to its reciprocal return probability.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 #442, proof of Lemma 6.5, PDF p. 27, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib
open MeasureTheory
open scoped ENNReal Interval

theorem CountingLLL.ContractedWalk.pgf_reciprocal_expectation {β : Type} [MeasurableSpace β] (ν : Measure β) [IsProbabilityMeasure ν]
    (K : β → ℕ) (hK : Measurable K) :
    (∫ x, (1:ℝ)/((K x : ℝ)+1) ∂ν) = ∫ z in (0:ℝ)..1, ∫ x, z ^ K x ∂ν := by sorry
