-- Prove2me | Theorems.Thm_CountingLLL_RandomRAM_branching_expected_work
-- name    : CountingLLL.RandomRAM.branching_expected_work
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:03:47.457326+00:00
-- url     : https://prove2.me/theorems/f1e8e3b2-52b2-49d2-a94f-2e543475d1cb
-- title:
--   Expected work under subcritical generation bounds
-- statement:
--   Let Z_n and Work_n be measurable nonnegative extended-real generation sizes and local work on a measure space. If E[Z_0]<=1, E[Z_(n+1)]<=E[Z_n]/8, and E[Work_n]<=C E[Z_n] for every n, then the expected total number of invocations is at most 8/7 and expected total work is at most 8C/7. No independence is assumed. This formalizes the final geometric-branching step of Lemma 5.7, conditional on establishing the generation and local-work inequalities for the adaptive recursive estimator.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovasz Local Lemma, STOC submission #442, proof of Lemma 5.7, Section 5.2.3, PDF p.20, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib
open MeasureTheory
open scoped ENNReal

theorem CountingLLL.RandomRAM.branching_expected_work {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z Work : ℕ → Ω → ℝ≥0∞) (C : ℝ≥0∞)
    (hZ : ∀ n, Measurable (Z n)) (hWork : ∀ n, Measurable (Work n))
    (h0 : (∫⁻ ω, Z 0 ω ∂μ) ≤ 1)
    (hstep : ∀ n, (∫⁻ ω, Z (n+1) ω ∂μ) ≤ (1/8 : ℝ≥0∞) * (∫⁻ ω, Z n ω ∂μ))
    (hcost : ∀ n, (∫⁻ ω, Work n ω ∂μ) ≤ C * (∫⁻ ω, Z n ω ∂μ)) :
    (∫⁻ ω, ∑' n, Z n ω ∂μ) ≤ (8/7 : ℝ≥0∞) ∧
    (∫⁻ ω, ∑' n, Work n ω ∂μ) ≤ C * (8/7 : ℝ≥0∞) := by sorry
