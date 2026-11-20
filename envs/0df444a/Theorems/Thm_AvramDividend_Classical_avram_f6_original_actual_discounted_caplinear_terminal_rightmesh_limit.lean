-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_actual_discounted_caplinear_terminal_rightmesh_limit
-- name    : AvramDividend.Classical.avram_f6_original_actual_discounted_caplinear_terminal_rightmesh_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T17:28:39.2571+00:00
-- url     : https://prove2.me/theorems/8d96da8b-12f4-4cc1-86b5-29a5d40a7942
-- title:
--   Original true discounted caplinear terminal at physical rightmesh converges through ruin branch
-- statement:
--   For the original admissible dividend strategy and reserve, the real discounted exact all-cap HJB terminal along ρm=min(τ,σ+1/(m+1)) converges to the terminal at σ≤τ≤ruin. Handles σ=τ (exact ruin contact and atom) by eventual identity and σ<τ using strict pre-ruin postpayment solvency and proved original path right-continuity, without any assumed martingale estimate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_true_ruinbranch_rightmesh_converges
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_caplinear_discounted_terminal_continuous_limit
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_rightmesh_eventually_below_strict_horizon
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_delayed_clock_real_min_tends_to_stopped
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_closed_preruin_actual_postpayment_solvency
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_actual_discounted_caplinear_terminal_rightmesh_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (ω : Ω) (σ τ : ℝ≥0)
    (hστ : σ ≤ τ) (hτruin : (τ : ℝ≥0∞) ≤ ruinTime X x D ω) :
    let ρ : ℕ → ℝ≥0 := fun m =>
      min τ (σ + (1 : ℝ≥0) / ((m : ℝ≥0) + 1))
    let W : ℝ≥0 → ℝ := fun t =>
      if t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X t ω - rightLimit D t ω
      else riskProcess X x D t ω
    let V : ℝ → ℝ := fun z =>
      if ENNReal.ofReal z ≤ C then w z
      else w C.toReal + (z - C.toReal)
    Tendsto (fun m => Real.exp (-(q * (ρ m : ℝ))) * V (W (ρ m)))
      atTop (𝓝 (Real.exp (-(q * (σ : ℝ))) * V (W σ))) := by sorry
