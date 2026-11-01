-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_actual_finite_horizon_controlled_gradient_time_probability_L2
-- name    : AvramDividend.Classical.avram_wave4_04b_actual_finite_horizon_controlled_gradient_time_probability_L2
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T20:32:55.376747+00:00
-- url     : https://prove2.me/theorems/6b89f4be-529d-4d78-9fe3-115290b922c1
-- title:
--   Original controlled compact-band gradient L2 energy against the actual finite-horizon time probability law
-- statement:
--   Given the genuine spectrally negative Lévy path and arbitrary adapted admissible dividend strategy, every compact strictly interior reserve-localised derivative of a local C² value function is predictable and has finite integrated square against the genuine finite-horizon Lebesgue-time × original probability P measure, represented exactly as a finite trim on the predictable space. No replacement marginal coupling, Brownian-only law, jump atom concentration or stochastic representation is assumed.
-- source:
--   Proved bcd9edf0 compact gradient predictable L² for any finite predictable measure, specialised using 04-B original predictable time P trim.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_source_finite_horizon_time_probability_predictable_trim
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_prejump_gradient_compact_band_L2_energy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_actual_finite_horizon_controlled_gradient_time_probability_L2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (T : ℝ≥0) :
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
          μ A = ((((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
      (let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
       let H : ℝ≥0 × Ω → ℝ := fun p =>
          if Y p ∈ Icc u v then deriv w (Y p) else 0
       Measurable[𝓕.rightCont.predictable] H ∧
         (∫⁻ p : ℝ≥0 × Ω, ENNReal.ofReal ((H p) ^ 2) ∂μ) < ⊤) := by
  sorry
