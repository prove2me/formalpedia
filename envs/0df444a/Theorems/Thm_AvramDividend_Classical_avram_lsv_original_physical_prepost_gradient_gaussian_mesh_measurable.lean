-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsv_original_physical_prepost_gradient_gaussian_mesh_measurable
-- name    : AvramDividend.Classical.avram_lsv_original_physical_prepost_gradient_gaussian_mesh_measurable
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T22:10:15.19501+00:00
-- url     : https://prove2.me/theorems/8c785e40-0339-4e1f-aa44-13b4de960b45
-- title:
--   Actual original physical prepost Gaussian first-Hermite gradient-error mesh is globally measurable for every fixed mesh
-- statement:
--   For arbitrary real w, actual original spectrally negative Levy X with its original adaptedness, any original dividend strategy and right-continuous stopping time rho, the finite physical grid nonnegative first-Hermite absolute prepayment-postpayment derivative difference sum is measurable. Uses measurable_deriv for every real function, adapted X and D, rightLimit D adapted rightCont, and rho stopping-time measurability, without any moment or Gaussian assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_adapted_rightCont
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_lsv_original_physical_prepost_gradient_gaussian_mesh_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0))) :
    let Elinear : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let Z := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
        let U := Z ^ 2 - (Δ : ℝ) * X.σ ^ 2
        let ypost := x + X.X s ω - rightLimit D s ω
        let ypre := riskProcess X x D s ω
        let e : ℝ := if s < ρ ω then Real.exp (-(q * (s : ℝ))) else 0
        |e| * |deriv w ypost - deriv w ypre| * |Z|
    ∀ m : ℕ, Measurable (Elinear m) := by sorry
