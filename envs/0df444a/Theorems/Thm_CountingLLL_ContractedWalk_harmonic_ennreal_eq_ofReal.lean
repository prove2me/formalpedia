-- Prove2me | Theorems.Thm_CountingLLL_ContractedWalk_harmonic_ennreal_eq_ofReal
-- name    : CountingLLL.ContractedWalk.harmonic_ennreal_eq_ofReal
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:07:58.262505+00:00
-- url     : https://prove2.me/theorems/baab12fb-3a70-498d-b340-0e1ebec78d75
-- title:
--   Real and nonnegative-real harmonic expectations agree
-- statement:
--   Let $K$ be a measurable nonnegative integer-valued random variable on a probability space with finite expectation. The extended-nonnegative expectation of $\sum_{k<K}1/(k+2)$ equals the embedding into the extended nonnegative reals of its real expectation.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, proof of Lemma 6.5, calls to O, p. 28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib
open MeasureTheory
open scoped BigOperators ENNReal

theorem CountingLLL.ContractedWalk.harmonic_ennreal_eq_ofReal {β : Type*} [MeasurableSpace β]
    (ν : Measure β) [IsProbabilityMeasure ν]
    (K : β → ℕ) (hK : Measurable K) (hKi : Integrable (fun x => (K x : ℝ)) ν) :
    (∫⁻ x, ∑ k ∈ Finset.range (K x), (((k+2 : ℕ) : ℝ≥0∞)⁻¹) ∂ν) =
      ENNReal.ofReal (∫ x, ∑ k ∈ Finset.range (K x), (1:ℝ)/(k+2) ∂ν) := by sorry
