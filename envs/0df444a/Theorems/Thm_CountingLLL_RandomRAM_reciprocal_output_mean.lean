-- Prove2me | Theorems.Thm_CountingLLL_RandomRAM_reciprocal_output_mean
-- name    : CountingLLL.RandomRAM.reciprocal_output_mean
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:39:42.813738+00:00
-- url     : https://prove2.me/theorems/52edcb82-62b5-4df1-b7ac-616718688540
-- title:
--   Mean of the zero-terminated reciprocal estimator
-- statement:
--   Let nu be a probability distribution on the reals with finite second moment M<1 and mean r in [0,1). On an independent stream of samples, write P_0=1 and P_n for the product of the first n samples, and let W be the sum of the P_n. Then W is integrable and has expectation 1/(1-r). Whenever a sample at index k is zero, W equals the finite sum through P_k, exactly the value produced by stopping at that zero. The separate almost-sure stopping theorem applies when nu(Y != 0)<1. This establishes the first-moment portion of Lemma 5.4 without assuming Y is nonnegative.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovasz Local Lemma, STOC submission #442, Lemma 5.4, equation (27), Section 5.2.1, PDF p.18, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

theorem CountingLLL.RandomRAM.reciprocal_output_mean (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : MemLp (fun x : ℝ => x) 2 ν)
    (hr0 : 0 ≤ ∫ x, x ∂ν) (hr1 : (∫ x, x ∂ν) < 1)
    (hM : (∫ x, x ^ 2 ∂ν) < 1) :
    let W : (ℕ → ℝ) → ℝ := fun ω => ∑' n : ℕ, ∏ j : Fin n, ω j.val
    Integrable W (Measure.infinitePi fun _ : ℕ => ν) ∧
    (∫ ω, W ω ∂(Measure.infinitePi fun _ : ℕ => ν)) = (1 - ∫ x, x ∂ν)⁻¹ ∧
    (∀ (ω : ℕ → ℝ) (k : ℕ), ω k = 0 →
      W ω = ∑ n ∈ Finset.range (k + 1), ∏ j : Fin n, ω j.val) := by sorry
