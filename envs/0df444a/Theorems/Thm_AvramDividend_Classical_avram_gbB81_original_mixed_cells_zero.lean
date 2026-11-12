-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB81_original_mixed_cells_zero
-- name    : AvramDividend.Classical.avram_gbB81_original_mixed_cells_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T17:24:08.411981+00:00
-- url     : https://prove2.me/theorems/6265b22c-a613-4f7f-9c8b-cad9a2c8c990
-- title:
--   Distinct original uniform Gaussian cells have zero mixed predictable covariance
-- statement:
--   Original Gaussian mixed-cell cross expectation is zero for arbitrary distinct deterministic uniform grid indices and separately bounded predictable coefficients. Apply Proved original disjoint two-cell zero covariance with either temporal ordering.
-- source:
--   Root-connected children of gbB79 original finite-grid bilinear covariance

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB81_original_mixed_cells_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (n N : ℕ) (hn : 0 < n) (hN : 0 < N)
    (H J : ℕ → Ω → ℝ)
    (hHAdapt : ∀ (i : ℕ), Measurable[𝓕.rightCont ((i : ℝ≥0) * ((n : ℝ≥0) / (N : ℝ≥0)))] (H i))
    (hJAdapt : ∀ (i : ℕ), Measurable[𝓕.rightCont ((i : ℝ≥0) * ((n : ℝ≥0) / (N : ℝ≥0)))] (J i))
    (hHBound : ∃ B : ℝ, 0 ≤ B ∧ ∀ i ω, |H i ω| ≤ B)
    (hJBound : ∃ B : ℝ, 0 ≤ B ∧ ∀ i ω, |J i ω| ≤ B) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / (N : ℝ≥0)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let Z : ℕ → Ω → ℝ := fun i ω => X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c
    ∀ i j : ℕ, i ≠ j →
      (∫ ω, (H i ω * Z i ω) * (J j ω * Z j ω) ∂P) = 0 := by sorry
