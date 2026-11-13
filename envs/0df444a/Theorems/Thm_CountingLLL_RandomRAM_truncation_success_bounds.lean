-- Prove2me | Theorems.Thm_CountingLLL_RandomRAM_truncation_success_bounds
-- name    : CountingLLL.RandomRAM.truncation_success_bounds
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:08:54.60367+00:00
-- url     : https://prove2.me/theorems/d4bc6450-adae-44af-b9d7-650c36ea14bc
-- title:
--   Two-cutoff truncation for arbitrary expected-cost bounds
-- statement:
--   Let G have probability at least 15/16, and let f and g be measurable nonnegative extended-real costs whose expectations are at most positive finite bounds B_f and B_g. Then the event that G occurs, f is below 16 B_f, and g is below 16 B_g has probability at least 13/16. This establishes the two-cost truncation step in the randomized approximate-counting proof; it does not require independence.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovasz Local Lemma, STOC submission #442, proof of Theorem 1.3, Section 5.3, PDF p.21, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib
open MeasureTheory
open scoped ENNReal

theorem CountingLLL.RandomRAM.truncation_success_bounds {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (G : Set Ω) (f g : Ω → ℝ≥0∞) (Bf Bg : ℝ≥0∞)
    (hBf0 : Bf ≠ 0) (hBg0 : Bg ≠ 0) (hBft : Bf ≠ ⊤) (hBgt : Bg ≠ ⊤)
    (hf : Measurable f) (hg : Measurable g)
    (hEf : ∫⁻ ω, f ω ∂μ ≤ Bf) (hEg : ∫⁻ ω, g ω ∂μ ≤ Bg)
    (hgood : (15 / 16 : ℝ≥0∞) ≤ μ G) :
    (13 / 16 : ℝ≥0∞) ≤ μ {ω | ω ∈ G ∧ f ω < 16 * Bf ∧ g ω < 16 * Bg} := by sorry
