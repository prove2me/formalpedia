-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_ruin_stopped_full_jump_l2_energy
-- name    : AvramDividend.Classical.avram_wave5_03_actual_ruin_stopped_full_jump_l2_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T00:51:05.325995+00:00
-- url     : https://prove2.me/theorems/1a78b825-d059-46e0-a1f7-0c8d88063a00
-- title:
--   Actual ruin-stopped controlled full negative-jump kernel is predictable and square-integrable
-- statement:
--   For the original SpectrallyNegativeLevy X, adapted dividend strategy D and its actual endogenous ruinTime, the controlled pre-jump value increment on a compact strict interior reserve band, multiplied by the inclusive survival indicator 1_{t≤ruinTime}, remains predictable-mark measurable and has finite nested square energy against the actual source negative-mark Lévy measure and every finite source predictable observation measure. The stopping includes the ruin-causing source jump, while the separate Stieltjes dividend payment convention excludes its positive terminal right payment. No PRM or martingale is assumed.
-- source:
--   Proved actual ruinTime stopping time 0e921b75 and inclusive survival strong predictability 69806d16, combined with original controlled full negative-mark finite quadratic energy 18dba881. Direct parent usefulness: corrected UBV 429e17ca, BV ef7e6c20, and stopped-martingale P1; does not establish compensator or Ito formula.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_controlled_predictable_full_negative_mark_energy_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_inclusiveSurvival_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_actual_ruinTime_rightCont_stopping_time

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_actual_ruin_stopped_full_jump_l2_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v δ : ℝ)
    (hw : ContDiffOn ℝ 1 w (Ioo a b))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (hu0 : 0 ≤ u)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hband : u + δ ≤ v)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let J : ((ℝ≥0 × Ω) × ℝ) → ℝ :=
      fun p => if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * J p
    Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] H ∧
      (∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in Iio (0 : ℝ),
          ENNReal.ofReal ((H (p, z)) ^ 2) ∂X.ν ∂μ) < ⊤ := by
  sorry
