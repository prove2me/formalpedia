-- Prove2me | Theorems.Thm_CountingLLL_RandomRAM_reciprocal_second_moment
-- name    : CountingLLL.RandomRAM.reciprocal_second_moment
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:48:11.134404+00:00
-- url     : https://prove2.me/theorems/67d5e1d0-59ce-43ab-9e82-f2863180a885
-- title:
--   Second moment of the zero-terminated reciprocal estimator
-- statement:
--   Let Y_1,Y_2,... be independent samples from a real probability law with finite second moment M<1, mean r in [0,1), and probability of nonzero output tau<1. Let P_0=1, P_n=Y_1...Y_n, and W be the sum of the prefix products. Then W squared is integrable and its expectation is (1+r)/((1-r)(1-M)). The almost-sure stopping theorem identifies the infinite sum with the finite zero-terminated algorithm. The separate stopping, first moment, cost, cross moments and triangular-series results are available on Prove2Me; the remaining bridge to this squared-output claim is open.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovasz Local Lemma, STOC submission #442, Lemma 5.4, equation (27), Section 5.2.1, PDF p.18, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

theorem CountingLLL.RandomRAM.reciprocal_second_moment (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : MemLp (fun x : ℝ => x) 2 ν)
    (hr0 : 0 ≤ ∫ x, x ∂ν) (hr1 : (∫ x, x ∂ν) < 1)
    (hM : (∫ x, x ^ 2 ∂ν) < 1) (hτ : ν {x | x ≠ 0} < 1) :
    let μ : Measure (ℕ → ℝ) := Measure.infinitePi fun _ : ℕ => ν
    let r : ℝ := ∫ x, x ∂ν
    let M : ℝ := ∫ x, x ^ 2 ∂ν
    let W : (ℕ → ℝ) → ℝ := fun ω => ∑' n : ℕ, ∏ k ∈ Finset.range n, ω k
    Integrable (fun ω => (W ω) ^ 2) μ ∧
    (∫ ω, (W ω) ^ 2 ∂μ) = (1 + r) / ((1 - r) * (1 - M)) := by sorry
