-- Prove2me | Theorems.Thm_CountingLLL_RandomRAM_reciprocal_prefix_cross_moments
-- name    : CountingLLL.RandomRAM.reciprocal_prefix_cross_moments
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:44:02.060142+00:00
-- url     : https://prove2.me/theorems/b7972004-52c9-4715-b289-f0a724cd2d41
-- title:
--   Cross moments of reciprocal-estimator prefix products
-- statement:
--   Let Y_1,Y_2,... be independent samples from a real distribution with finite second moment M and mean r, and put P_0=1 and P_n=Y_1...Y_n. Then every P_i P_(i+j) is integrable and has expectation M^i r^j. Its absolute expectation equals M^i (E|Y|)^j. The absolute-moment identity is the summability ingredient used to justify the double-series interchange in the second-moment calculation of Lemma 5.4. No nonnegativity assumption is imposed on Y.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovasz Local Lemma, STOC submission #442, proof of Lemma 5.4, Section 5.2.1, PDF p.18, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

theorem CountingLLL.RandomRAM.reciprocal_prefix_cross_moments (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : MemLp (fun x : ℝ => x) 2 ν) (i j : ℕ) :
    Integrable (fun ω : ℕ → ℝ => (∏ k ∈ Finset.range i, ω k) *
      (∏ k ∈ Finset.range (i+j), ω k)) (Measure.infinitePi fun _ : ℕ => ν) ∧
    (∫ ω, (∏ k ∈ Finset.range i, ω k) * (∏ k ∈ Finset.range (i+j), ω k)
      ∂(Measure.infinitePi fun _ : ℕ => ν)) =
      (∫ x, x ^ 2 ∂ν) ^ i * (∫ x, x ∂ν) ^ j ∧
    (∫ ω, |(∏ k ∈ Finset.range i, ω k) * (∏ k ∈ Finset.range (i+j), ω k)|
      ∂(Measure.infinitePi fun _ : ℕ => ν)) =
      (∫ x, x ^ 2 ∂ν) ^ i * (∫ x, |x| ∂ν) ^ j := by sorry
