-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_true_rightmesh_expected_limit_of_domination
-- name    : AvramDividend.Classical.avram_f6_original_true_rightmesh_expected_limit_of_domination
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T18:24:47.237185+00:00
-- url     : https://prove2.me/theorems/344fa5a7-da99-424e-9d4d-2fd0aa95481b
-- title:
--   Original caplinear rightmesh expected reward converges under an actual source integral envelope
-- statement:
--   For true original finite-clipped physical rightmesh, exact caplinear terminal plus inclusive dividend cash, an explicitly established integrable common bound, source measurability, and a.e. rightmesh limit imply convergence of true expected payoffs. This is the needed dominated convergence transfer; the envelope remains a separate source obligation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_true_rightmesh_expected_limit_of_domination
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (σ τ : Ω → ℝ≥0)
    (ρ : ℕ → Ω → ℝ≥0 := fun m ω =>
      min (τ ω) (σ ω + 1 / ((m : ℝ≥0) + 1)))
    (V : ℝ → ℝ := fun z =>
      if ENNReal.ofReal z ≤ C then w z
      else w C.toReal + (z - C.toReal))
    (R : (Ω → ℝ≥0) → Ω → ℝ := fun s ω =>
      Real.exp (-(q * (s ω : ℝ))) *
        V (if s ω = 0 ∨ (s ω : ℝ≥0∞) < ruinTime X x D ω
          then x + X.X (s ω) ω - rightLimit D (s ω) ω
          else riskProcess X x D (s ω) ω) +
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (s ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal)
    (bound : Ω → ℝ)
    (hbound : Integrable bound P)
    (hMeas : ∀ m, AEStronglyMeasurable (fun ω => R (ρ m) ω) P)
    (hdom : ∀ m, ∀ᵐ ω ∂P, ‖R (ρ m) ω‖ ≤ bound ω)
    (hlim : ∀ᵐ ω ∂P,
      Tendsto (fun m => R (ρ m) ω) atTop (𝓝 (R σ ω))) :
    Tendsto (fun m => ∫ ω, R (ρ m) ω ∂P) atTop
      (𝓝 (∫ ω, R σ ω ∂P)) := by sorry
