-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_stopped_grid_summable_L2_tail_limit_mean_zero
-- name    : AvramDividend.Classical.avram_wave7_06_original_stopped_grid_summable_L2_tail_limit_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:54:54.87792+00:00
-- url     : https://prove2.me/theorems/237e674b-3a93-40f9-96a5-bac0f142d273
-- title:
--   Summable L2 successive tails give original stopped predictable grid zero-mean limit
-- statement:
--   For the authentic original spectrally negative Levy source X and stopped predictable scalar grid weights, explicit summability of successive L2(P) distances is a sufficient finite-band tail bound. Each approximant is represented exactly almost everywhere by a concrete stopped source finite-grid sum; original past measurability and integrability ensure zero mean, and summable L2 distances imply Cauchy convergence to an L2(P) zero-mean limit. This bridges a checkable quantitative tail criterion to L1 expectation passage, but no Poisson marked-band tail estimate is claimed without the intrinsic source jump law.
-- source:
--   W7-06 source stopped predictable truncation L2/L1 limit under explicit quantitative summable tail certificate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_stopped_grid_summable_L2_tail_limit_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℕ → ℕ) (s t : ℕ → ℕ → ℝ≥0)
    (H : ℕ → ℕ → Ω → ℝ) (τ : Ω → ℕ)
    (hWPast : ∀ k, ∀ i ∈ Finset.range (n k),
      Measurable[𝓕 (s k i)]
        (fun ω => if i < τ ω then H k i ω else 0))
    (hWI : ∀ k, ∀ i ∈ Finset.range (n k),
      Integrable (fun ω => if i < τ ω then H k i ω else 0) P)
    (hXI : ∀ k, ∀ i ∈ Finset.range (n k),
      Integrable (X.X (t k i)) P)
    (hCellI : ∀ k, ∀ i ∈ Finset.range (n k), Integrable (fun ω =>
      (if i < τ ω then H k i ω else 0) *
        (X.X (s k i + t k i) ω - X.X (s k i) ω -
          (∫ η, X.X (t k i) η ∂P))) P)
    (M : ℕ → Lp ℝ (2 : ℝ≥0∞) P)
    (hSource : ∀ k, (M k : Ω → ℝ) =ᵐ[P] fun ω =>
      ∑ i ∈ Finset.range (n k),
        (if i < τ ω then H k i ω else 0) *
          (X.X (s k i + t k i) ω - X.X (s k i) ω -
            (∫ η, X.X (t k i) η ∂P)))
    (hTail : Summable (fun k => dist (M k) (M (k + 1)))) :
    ∃ L : Lp ℝ (2 : ℝ≥0∞) P,
      Tendsto M Filter.atTop (𝓝 L) ∧
      (∫ ω, L ω ∂P) = 0 := by sorry
