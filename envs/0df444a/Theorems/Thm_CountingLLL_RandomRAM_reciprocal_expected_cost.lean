-- Prove2me | Theorems.Thm_CountingLLL_RandomRAM_reciprocal_expected_cost
-- name    : CountingLLL.RandomRAM.reciprocal_expected_cost
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:35:43.44242+00:00
-- url     : https://prove2.me/theorems/13fc16f2-5c21-47a5-8481-d0872a0d7611
-- title:
--   Expected cost of a zero-terminated independent-sample process
-- statement:
--   Let independent identically distributed samples take values in an arbitrary measurable space with law nu. Each sample is marked by a measurable nonnegative cost K, which may depend arbitrarily on that same sample. Continue while preceding samples lie in a measurable set S, and charge each requested sample including the first sample outside S. The expected total cost equals E[K]/(1-nu(S)), with extended-nonnegative-real conventions, including infinite expectations. The proof uses independence across samples and does not assume independence between a sample and its own cost. This establishes the cost calculation in Lemma 5.4 for S={Y != 0}.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovasz Local Lemma, STOC submission #442, Lemma 5.4 and proof, Section 5.2.1, PDF p.18, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

theorem CountingLLL.RandomRAM.reciprocal_expected_cost {β : Type} [MeasurableSpace β] (ν : Measure β) [IsProbabilityMeasure ν]
    (S : Set β) (hS : MeasurableSet S) (K : β → ℝ≥0∞) (hK : Measurable K) :
    (∫⁻ ω, ∑' n : ℕ,
      ({ω' : ℕ → β | ∀ i < n, ω' i ∈ S}).indicator (fun ω => K (ω n)) ω
      ∂(Measure.infinitePi fun _ : ℕ => ν)) =
      (∫⁻ x, K x ∂ν) / (1 - ν S) := by sorry
