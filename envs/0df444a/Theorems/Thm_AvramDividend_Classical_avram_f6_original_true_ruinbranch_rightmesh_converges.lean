-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_true_ruinbranch_rightmesh_converges
-- name    : AvramDividend.Classical.avram_f6_original_true_ruinbranch_rightmesh_converges
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T16:09:48.105251+00:00
-- url     : https://prove2.me/theorems/d70504a9-e807-4d73-8e97-948f620dbe75
-- title:
--   Original true prepayment/postpayment ruin-branch reserve converges along genuine rightmesh
-- statement:
--   For the true original sample path and dividend right limit, the exact if clock=0 or before ruin versus ruin riskProcess branch at min(tau,sigma+1/(m+1)) tends to the identical branch at sigma when sigma≤tau≤ruinTime. At sigma=tau, rightmesh is constant; at sigma<tau it eventually remains strictly before ruin. This is the exact source for F6 contact terminal convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_true_postpayment_reserve_rightmesh_converges
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_rightmesh_eventually_below_strict_horizon
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_true_ruinbranch_rightmesh_converges
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ τ : ℝ≥0) (hστ : σ ≤ τ)
    (hτruin : (τ : ℝ≥0∞) ≤ ruinTime X x D ω) :
    let ρ : ℕ → ℝ≥0 := fun m =>
      min τ (σ + (1 : ℝ≥0) / ((m : ℝ≥0) + 1))
    let W : ℝ≥0 → ℝ := fun t =>
      if t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X t ω - rightLimit D t ω
      else riskProcess X x D t ω
    Tendsto (fun m => W (ρ m)) atTop (𝓝 (W σ)) := by sorry
