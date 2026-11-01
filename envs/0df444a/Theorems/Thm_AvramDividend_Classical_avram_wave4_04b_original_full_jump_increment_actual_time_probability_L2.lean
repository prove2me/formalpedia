-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_original_full_jump_increment_actual_time_probability_L2
-- name    : AvramDividend.Classical.avram_wave4_04b_original_full_jump_increment_actual_time_probability_L2
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T22:35:45.224201+00:00
-- url     : https://prove2.me/theorems/8a2c6c5a-8b13-4ed1-be3a-55fca4a7d955
-- title:
--   Actual controlled full Lévy jump increment finite square energy under literal source time probability
-- statement:
--   On the original same-probability adapted Lévy and arbitrary admissible full Stieltjes dividend control, the strict-prejump localised full negative-jump value increment J is joint predictable×mark measurable and square integrable against the literal finite-horizon Lebesgue-time×original P and the original Lévy jump measure. This is the genuine compensated-PRM stochastic integrand, retaining all ruin-crossing marks, not merely the Taylor generator remainder; no PRM or martingale is postulated.
-- source:
--   Proved original full negative mark predictable nested energy 18dba881, source time P predictable-lintegral equality 16857b34, original negative signed Lévy SigmaFinite c93daaa4, Mathlib measurable inner lintegral.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_negative_levy_measure_sigmaFinite
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_source_finite_horizon_predictable_lintegral_eq_time_probability
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_controlled_predictable_full_negative_mark_energy_finite

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_original_full_jump_increment_actual_time_probability_L2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (hu0 : 0 ≤ u)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hband : u + δ ≤ v)
    (T : ℝ≥0) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let J : ((ℝ≥0 × Ω) × ℝ) → ℝ :=
      fun p => if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0
    Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] J ∧
      (∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in Iio (0 : ℝ),
          ENNReal.ofReal ((J (p, z)) ^ 2) ∂X.ν
          ∂((((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal).prod P)) < ⊤ := by
  sorry
