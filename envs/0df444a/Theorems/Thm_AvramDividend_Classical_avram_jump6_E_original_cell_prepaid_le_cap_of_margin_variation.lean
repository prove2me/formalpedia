-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_E_original_cell_prepaid_le_cap_of_margin_variation
-- name    : AvramDividend.Classical.avram_jump6_E_original_cell_prepaid_le_cap_of_margin_variation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T08:03:05.115661+00:00
-- url     : https://prove2.me/theorems/9fd774e8-69af-4a25-ac4e-6d7e81070c21
-- title:
--   Original stopped prepayment reserve below cap from postpayment margin and actual dividend variation
-- statement:
--   Sound original stopped canonical physical-grid upper bound for prepayment reserve. If each postpayment reserve stays at least delta below the finite cap and the actual right-limit dividend increase across that cell is at most delta, then the corresponding original prepayment reserve lies below cap. The result preserves the exact Levy increments, stopped mesh and right-limit dividend convention. It provides explicit hypotheses to invoke the original raw-w versus caplinear-V equality; it does not claim finite-cap admissibility alone controls raw prepayment reserves.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_E_original_cell_prepaid_le_cap_of_margin_variation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0)
    (ω : Ω) (n j : ℕ) (δ : ℝ)
    (hMargin : ∀ i < (n + 1) * (j + 1),
      x + X.X (min (((i + 1 : ℕ) : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) (τ ω)) ω -
        rightLimit D (min (((i + 1 : ℕ) : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) (τ ω)) ω
        ≤ C.toReal - δ)
    (hVariation : ∀ i < (n + 1) * (j + 1),
      rightLimit D (min (((i + 1 : ℕ) : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) (τ ω)) ω -
        rightLimit D (min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) (τ ω)) ω ≤ δ) :
    ∀ i < (n + 1) * (j + 1),
      x + X.X (min (((i + 1 : ℕ) : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) (τ ω)) ω -
        rightLimit D (min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) (τ ω)) ω ≤ C.toReal := by sorry
