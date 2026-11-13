-- Prove2me | Theorems.Thm_CountingLLL_RandomRAM_reciprocal_cross_series
-- name    : CountingLLL.RandomRAM.reciprocal_cross_series
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:46:50.652892+00:00
-- url     : https://prove2.me/theorems/773dd304-3b28-490a-9bd3-d6af718b9bbe
-- title:
--   Summability of reciprocal-estimator cross moments
-- statement:
--   For independent samples of a square-integrable real variable with mean r in [0,1) and second moment M<1, let P_n be the nth prefix product and q=E|Y|. The doubly indexed upper-triangular absolute cross moments E|P_i P_(i+j)| are summable, and their sum equals 1/((1-M)(1-q)). The signed upper-triangular cross moments are also summable with sum 1/((1-M)(1-r)); twice that sum minus the diagonal geometric sum equals (1+r)/((1-r)(1-M)). This proves the summability and series evaluation used in the proof of Lemma 5.4, but it does not itself identify the series with E[W^2].
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovasz Local Lemma, STOC submission #442, proof of Lemma 5.4, equation (27), Section 5.2.1, PDF p.18, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

theorem CountingLLL.RandomRAM.reciprocal_cross_series (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : MemLp (fun x : ℝ => x) 2 ν)
    (hr0 : 0 ≤ ∫ x, x ∂ν) (hr1 : (∫ x, x ∂ν) < 1)
    (hM : (∫ x, x ^ 2 ∂ν) < 1) :
    let μ : Measure (ℕ → ℝ) := Measure.infinitePi fun _ : ℕ => ν
    let M : ℝ := ∫ x, x ^ 2 ∂ν
    let r : ℝ := ∫ x, x ∂ν
    let q : ℝ := ∫ x, |x| ∂ν
    let C : ℕ × ℕ → ℝ := fun ij => ∫ ω,
      (∏ k ∈ Finset.range ij.1, ω k) * (∏ k ∈ Finset.range (ij.1 + ij.2), ω k) ∂μ
    let A : ℕ × ℕ → ℝ := fun ij => ∫ ω,
      |(∏ k ∈ Finset.range ij.1, ω k) * (∏ k ∈ Finset.range (ij.1 + ij.2), ω k)| ∂μ
    Summable A ∧ Summable C ∧
    (∑' ij, A ij) = (1 - M)⁻¹ * (1 - q)⁻¹ ∧
    (∑' ij, C ij) = (1 - M)⁻¹ * (1 - r)⁻¹ ∧
    2 * (∑' ij, C ij) - (1 - M)⁻¹ = (1 + r) / ((1 - r) * (1 - M)) := by sorry
