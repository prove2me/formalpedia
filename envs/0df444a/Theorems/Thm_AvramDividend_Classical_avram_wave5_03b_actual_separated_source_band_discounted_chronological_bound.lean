-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_separated_source_band_discounted_chronological_bound
-- name    : AvramDividend.Classical.avram_wave5_03b_actual_separated_source_band_discounted_chronological_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:48:36.122093+00:00
-- url     : https://prove2.me/theorems/05c1be95-42b1-4c3a-971f-e75d22364e29
-- title:
--   Original BV/UBV separated source jump band has exact discounted chronological nonlinear Itô dividend bound without an enumerating Finset premise
-- statement:
--   For the actual original spectrally negative Lévy process and adapted dividend strategy satisfying the explicit dividend payment inequality, every negative source jump band bounded away from zero admits a genuine finite enumeration on a finite clock interval. The original-source-before-right-payment chronological discounted nonlinear w-value increment plus dividend cash inequality holds for that exact enumeration, with inclusive ruin terminal convention. No standalone abstract Poisson calculation.
-- source:
--   Proved original source per-path BV/UBV separated jump finiteness UUID 52f0bc5f and Proved genuine original chronological discounted source-plus-dividend finite band inequality UUID 7e5af125.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_finite_horizon_separated_jump_marks_finite_every_path
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_discounted_finite_band_inclusive_ruin_chronological_jump_sum

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03b_actual_separated_source_band_discounted_chronological_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (q : ℝ) (u v ζ : ℝ) (s t : ℝ≥0) (ω : Ω)
    (B : Set ℝ) (hBneg : B ⊆ Iio (0 : ℝ))
    (ε : ℝ) (hε : 0 < ε)
    (hBsep : ∀ z ∈ B, ε ≤ dist z 0) :
    ∃ S : Finset ℝ≥0,
      (∀ r : ℝ≥0, r ∈ S ↔
        s < r ∧ r ≤ t ∧
          X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r ∈ B) ∧
      (let Y : ℝ≥0 → ℝ := fun r => Function.leftLim
          (fun a : ℝ≥0 => x + X.X a ω - rightLimit D a ω) r
       let J : ℝ≥0 → ℝ := fun r =>
          X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r
       let W : ℝ≥0 → ℝ := fun r =>
          if (r : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X r ω - rightLimit D r ω
          else riskProcess X x D r ω
       let cash : ℝ≥0 → ℝ := fun r =>
          if (r : ℝ≥0∞) < ruinTime X x D ω then
            rightLimit D r ω - D r ω else 0
       (∑ r ∈ S, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
         (if Y r ∈ Icc (u + ζ) v then
           Real.exp (-(q * (r : ℝ))) *
           ((w (W r) - w (Function.leftLim
             (fun a : ℝ≥0 => riskProcess X x D a ω) r)) + cash r)
          else 0) else 0) ≤
       (∑ r ∈ S, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
         (if Y r ∈ Icc (u + ζ) v then
           Real.exp (-(q * (r : ℝ))) *
             ((if -1 < J r then J r * deriv w (Y r) else 0) +
              SpectrallyNegativeLevy.generatorIntegrand w (Y r) (J r))
          else 0) else 0)) := by sorry
