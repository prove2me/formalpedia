-- Prove2me | Theorems.Thm_CountingLLL_ContractedWalk_harmonic_pgf_integral
-- name    : CountingLLL.ContractedWalk.harmonic_pgf_integral
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:06:47.729134+00:00
-- url     : https://prove2.me/theorems/3e3288ca-5c69-494f-bfac-dd5bdbd87766
-- title:
--   Harmonic expectation as a generating-function integral
-- statement:
--   Let $K$ be an integrable nonnegative integer-valued random variable. Its finite shifted harmonic sum satisfies $$\mathbb E\!\left[\sum_{k=0}^{K-1}\frac1{k+2}\right]=\int_0^1\frac{z(1-\mathbb E[z^K])}{1-z}\,dz.$$ The endpoint value is immaterial to the integral.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, proof of Lemma 6.5, calls to O, p. 28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib
open MeasureTheory
open scoped ENNReal Interval BigOperators

theorem CountingLLL.ContractedWalk.harmonic_pgf_integral {β : Type*} [MeasurableSpace β]
    (ν : Measure β) [IsProbabilityMeasure ν]
    (K : β → ℕ) (hK : Measurable K) (hKi : Integrable (fun x => (K x : ℝ)) ν) :
    (∫ x, ∑ k ∈ Finset.range (K x), (1 : ℝ)/(k+2) ∂ν) =
      ∫ z in (0:ℝ)..1, z*(1-(∫ x, z^K x ∂ν))/(1-z) := by sorry
