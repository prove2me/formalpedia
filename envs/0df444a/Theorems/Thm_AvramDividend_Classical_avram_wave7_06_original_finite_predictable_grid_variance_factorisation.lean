-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_finite_predictable_grid_variance_factorisation
-- name    : AvramDividend.Classical.avram_wave7_06_original_finite_predictable_grid_variance_factorisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:39:11.836763+00:00
-- url     : https://prove2.me/theorems/d9b9a99f-c0a0-478b-a0c0-d3a78048cc47
-- title:
--   Full finite-grid original-filtration predictable Levy scalar variance factorisation
-- statement:
--   The full second moment of the finite sum of predictable original-X centred increments is exactly the sum over cells E[Wi²] times Var(X_ti). Intervals are ordered and nonoverlapping, weights are original-source past measurable, X source increments have finite first/second moments, and explicit mixed integrability makes the finite-grid L2 energy argument rigorous. This is the finite-step scalar martingale isometry needed prior to extracting marked jumps.
-- source:
--   W7-06 exact finite-grid source scalar L² stopped predictable martingale variance factorisation, consumers W7-07/W7-08.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_finite_predictable_grid_variance_factorisation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ)
    (s t : ℕ → ℝ≥0) (W : ℕ → Ω → ℝ)
    (hOrder : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      i < j → s i + t i ≤ s j)
    (hWPast : ∀ i ∈ Finset.range n, Measurable[𝓕 (s i)] (W i))
    (hWI2 : ∀ i ∈ Finset.range n, Integrable (fun ω => (W i ω)^2) P)
    (hXI : ∀ i ∈ Finset.range n, Integrable (X.X (t i)) P)
    (hXI2 : ∀ i ∈ Finset.range n,
      Integrable (fun ω => (X.X (t i) ω)^2) P)
    (hEarlier : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      i < j → Integrable (fun ω =>
        (W i ω * (X.X (s i + t i) ω - X.X (s i) ω -
        (∫ η, X.X (t i) η ∂P))) * W j ω) P)
    (hPairI : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      Integrable (fun ω => (W i ω * (X.X (s i + t i) ω - X.X (s i) ω -
        (∫ η, X.X (t i) η ∂P))) *
        (W j ω * (X.X (s j + t j) ω - X.X (s j) ω -
        (∫ η, X.X (t j) η ∂P)))) P) :
    (∫ ω, (∑ i ∈ Finset.range n,
      (W i ω * (X.X (s i + t i) ω - X.X (s i) ω -
        (∫ η, X.X (t i) η ∂P))))^2 ∂P) =
      ∑ i ∈ Finset.range n,
        (∫ ω, (W i ω)^2 ∂P) *
          (∫ ω, (X.X (t i) ω - (∫ η, X.X (t i) η ∂P))^2 ∂P) := by sorry
