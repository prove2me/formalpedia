-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_ordered_predictable_weighted_cells_covariance_zero
-- name    : AvramDividend.Classical.avram_wave7_06_original_ordered_predictable_weighted_cells_covariance_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:33:41.549377+00:00
-- url     : https://prove2.me/theorems/a0bab660-3332-496a-8862-18f5a3c250a5
-- title:
--   Orthogonality of ordered nonoverlapping original-filtration predictable weighted Levy cells
-- statement:
--   Two source X centred increments on ordered disjoint time intervals have zero expected product after multiplication by predictable original-filtration scalar coefficients. This includes gaps between intervals, which permits pairwise orthogonality in arbitrary increasing finite grids. Explicit integrability of the first weighted centred cell times the later predictable weight supplies the necessary L1 factorisation.
-- source:
--   W7-06 ordered original scalar stopped predictable finite-grid martingale covariance zero for full-grid isometry.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_ordered_predictable_weighted_cells_covariance_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s₀ t₀ s₁ t₁ : ℝ≥0) (hOrder : s₀ + t₀ ≤ s₁)
    (W₀ W₁ : Ω → ℝ)
    (hW₀ : Measurable[𝓕 s₀] W₀)
    (hW₁ : Measurable[𝓕 s₁] W₁)
    (hXI : Integrable (X.X t₁) P)
    (hProduct : Integrable (fun ω =>
      (W₀ ω * (X.X (s₀ + t₀) ω - X.X s₀ ω -
        (∫ η, X.X t₀ η ∂P))) * W₁ ω) P) :
    (∫ ω, (W₀ ω * (X.X (s₀ + t₀) ω - X.X s₀ ω -
      (∫ η, X.X t₀ η ∂P))) *
      (W₁ ω * (X.X (s₁ + t₁) ω - X.X s₁ ω -
        (∫ η, X.X t₁ η ∂P))) ∂P) = 0 := by sorry
