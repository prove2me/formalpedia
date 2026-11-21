-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_E_original_grid_raw_eq_caplinear_belowcap_cells
-- name    : AvramDividend.Classical.avram_jump6_E_original_grid_raw_eq_caplinear_belowcap_cells
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T08:02:27.559215+00:00
-- url     : https://prove2.me/theorems/3f37444d-070c-4508-b858-af4c56ebf656
-- title:
--   Original stopped canonical raw/caplinear payment equality on cells below the finite cap
-- statement:
--   Exact original stopped physical-grid payment equality for finite-cap localisation: if the actual prepayment and postpayment reserves at each canonical cell endpoint are at most the cap, a caplinear extension V agrees with w on those endpoints, and the raw-w signed payment mesh equals the caplinear-V signed mesh. This is a conditional original Lévy-process statement, with identical right-limit dividend path D, stop τ and canonical grid, and avoids the false unrestricted raw-w payment bounds already retired. The hypotheses explicitly require prepayment control above cap rather than assuming it follows from IsAdmissibleLe; thus it supports interior-state localisation and can import existing Proved ce331276/e0170ed2 safely.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_E_original_grid_raw_eq_caplinear_belowcap_cells
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (C : ℝ≥0∞) (w V : ℝ → ℝ)
    (hV : ∀ y : ℝ, V y =
      if y ≤ C.toReal then w y else w C.toReal + (y - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0)
    (ω : Ω) (n j : ℕ)
    (hY : ∀ i < (n + 1) * (j + 1),
      x + X.X (min (((i + 1 : ℕ) : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) (τ ω)) ω -
        rightLimit D (min (((i + 1 : ℕ) : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) (τ ω)) ω ≤ C.toReal)
    (hZ : ∀ i < (n + 1) * (j + 1),
      x + X.X (min (((i + 1 : ℕ) : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) (τ ω)) ω -
        rightLimit D (min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) (τ ω)) ω ≤ C.toReal) :
    let v : ℕ → ℝ≥0 := fun i =>
      min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) (τ ω)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    let m : ℕ := (n + 1) * (j + 1)
    (∑ i ∈ Finset.range m,
      E (v (i + 1)) * (w (Y (v (i + 1))) - w (Z i))) =
    (∑ i ∈ Finset.range m,
      E (v (i + 1)) * (V (Y (v (i + 1))) - V (Z i))) := by sorry
