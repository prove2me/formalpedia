-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsv_original_preruin_dividend_gaussian_future_weighted_cell_L1
-- name    : AvramDividend.Classical.avram_lsv_original_preruin_dividend_gaussian_future_weighted_cell_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T17:24:37.64619+00:00
-- url     : https://prove2.me/theorems/ae6879a7-593b-4644-8dc8-b6b80a48b62e
-- title:
--   Original true stopped pre-ruin discounted dividend atom weighted Gaussian future absolute cell bound
-- statement:
--   For original X with zero Levy measure and positive Gaussian coefficient, original D and true ruin-bounded right-continuous stopping rho, the stopped discounted right-dividend atom H and centred source Gaussian future increment Z satisfy H|Z| and HZ squared integrability, and E[H|Z|] is at most sigma sqrt(Delta) E[H]. Original source exact without replacement processes.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_lsv_original_rightcont_discounted_preruin_single_atom_L2
import Theorems.Thm_AvramDividend_Classical_avram_lsv_original_zerojump_fixed_cell_second_fourth_power_integrable
import Theorems.Thm_AvramDividend_Classical_avram_lsv_original_rightcont_stopped_gaussian_weighted_sqrt_time_first_moment
import Theorems.Thm_AvramDividend_Classical_avram_ja20_integrable_product_of_square_integrable
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false
noncomputable section

theorem AvramDividend.Classical.avram_lsv_original_preruin_dividend_gaussian_future_weighted_cell_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hBV : ¬ X.BoundedVariation) (hσ : 0 < X.σ)
    (x : ℝ) (hx : 0 ≤ x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n s : ℝ≥0) (hsn : s ≤ n)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρruin : ∀ ω, (ρ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (q : ℝ) (hq : 0 ≤ q)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) :
    let H : Ω → ℝ := fun ω =>
      if s < ρ ω then
        Real.exp (-(q * (s : ℝ))) *
          (rightLimit D s ω - D s ω)
      else 0
    let Z : Ω → ℝ := fun ω =>
      X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
    Integrable (fun ω => H ω * |Z ω|) P ∧
      Integrable (fun ω => H ω * (Z ω)^2) P ∧
      (∫ ω, H ω * |Z ω| ∂P) ≤
        X.σ * Real.sqrt (Δ : ℝ) * (∫ ω, H ω ∂P) := by sorry
