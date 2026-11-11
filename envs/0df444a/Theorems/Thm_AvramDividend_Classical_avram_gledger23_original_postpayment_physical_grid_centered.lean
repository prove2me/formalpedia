-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger23_original_postpayment_physical_grid_centered
-- name    : AvramDividend.Classical.avram_gledger23_original_postpayment_physical_grid_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T15:11:19.429528+00:00
-- url     : https://prove2.me/theorems/9c81a232-e059-47bf-a4f5-ac49fb183f6b
-- title:
--   Original postpayment compact-clipped Gaussian physical grid has exactly zero mean
-- statement:
--   For the original X and original strategy D, each deterministic Gaussian grid increment before the actual right-continuous stopping clock is multiplied by the clipped derivative and Hessian evaluated at postpayment reserve x+X.X(s)-rightLimit D(s). The finite sum of linear centred increments and compensated squared increments is integrable and has expectation exactly zero. This directly matches chronological cell telescoping and removes the prepayment/postpayment coefficient mismatch for the root-connected Ito ledger.

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_avram_gledger23_original_postpayment_clipped_C2_coefficients
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_deterministic_increment_condExp_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_deterministic_quadratic_residual_condExp_zero
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger23_original_postpayment_physical_grid_centered
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (hx : 0 < x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (j n m : ℕ) :
    let a := min x ((1 : ℝ) / ((j : ℝ) + 1))
    let b := x + ((j : ℝ) + 1)
    let Y : ℝ≥0 → Ω → ℝ := fun t ω =>
      x + X.X t ω - rightLimit D t ω
    let interior : ℝ → Prop := fun y => 0 < y ∧ ENNReal.ofReal y < C
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let M : Ω → ℝ := fun ω => ∑ i ∈ Finset.range m,
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      if s < ρ ω ∧ Y s ω ∈ Icc a b then
        let z := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
        Real.exp (-(q * (s : ℝ))) *
          ((if interior (Y s ω) then deriv w (Y s ω) else 0) * z +
            ((if interior (Y s ω) then iteratedDeriv 2 w (Y s ω) else 0) / 2) *
              (z ^ 2 - (Δ : ℝ) * X.σ ^ 2))
      else 0
    Integrable M P ∧ (∫ ω, M ω ∂P) = 0 := by sorry
