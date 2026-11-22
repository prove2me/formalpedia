-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_oai_generic_centered_count_variance_from_factorial_identity_20261122
-- name    : AvramDividend.Classical.avram_oai_generic_centered_count_variance_from_factorial_identity_20261122
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T14:16:43.658709+00:00
-- url     : https://prove2.me/theorems/e1999c8a-6ec9-4d53-a408-d36a3a39a077
-- title:
--   Exact centred count variance from first and factorial second moments
-- statement:
--   If a real count N is integrable and its chronological unordered pair count K has finite expectation, E[N]=r, E[2K]=r² and N(N−1)=2K almost surely, then the exact centred second moment is integrable and E[(N−r)²]=r. This is the deterministic probability-analytic bridge from the original Lévy process finite negative Borel pathwise factorial-pair and ordered-pair moment theorems to the actual arbitrary-cell count variance, without requiring the full negative Lévy measure to have finite mass.

import Mathlib
open MeasureTheory
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_oai_generic_centered_count_variance_from_factorial_identity_20261122
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (N K : Ω → ℝ) (r : ℝ)
    (hN : Integrable N P)
    (hK : Integrable (fun ω => 2 * K ω) P)
    (hMean : (∫ ω, N ω ∂P) = r)
    (hPairs : (∫ ω, 2 * K ω ∂P) = r ^ 2)
    (hFactorial : ∀ᵐ ω ∂P, N ω * (N ω - 1) = 2 * K ω) :
    Integrable (fun ω => (N ω - r) ^ 2) P ∧
    (∫ ω, (N ω - r) ^ 2 ∂P) = r := by sorry
