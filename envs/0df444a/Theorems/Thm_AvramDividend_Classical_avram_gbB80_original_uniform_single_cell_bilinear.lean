-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB80_original_uniform_single_cell_bilinear
-- name    : AvramDividend.Classical.avram_gbB80_original_uniform_single_cell_bilinear
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T17:12:05.173817+00:00
-- url     : https://prove2.me/theorems/20a9306a-2709-4b68-a169-c49836904fde
-- title:
--   Original uniform grid single cell exact mixed Gaussian covariance
-- statement:
--   Prove exact sigma-squared covariance for one original-process Gaussian centred cell with two bounded predictable same-history weights via the Proved stopped-history bilinear covariance theorem.
-- source:
--   Direct children of published gbB77, upstream gbB76 original two-grid covariance

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB80_original_uniform_single_cell_bilinear
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
    ∀ i : ℕ, (∫ ω, (H i ω * Z i ω) * (J i ω * Z i ω) ∂P) =
      ((Δ : ℝ) * X.σ ^ 2) * (∫ ω, H i ω * J i ω ∂P) := by sorry
