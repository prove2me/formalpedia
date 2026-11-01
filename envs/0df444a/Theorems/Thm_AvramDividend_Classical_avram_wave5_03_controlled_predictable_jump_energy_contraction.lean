-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_controlled_predictable_jump_energy_contraction
-- name    : AvramDividend.Classical.avram_wave5_03_controlled_predictable_jump_energy_contraction
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T00:47:11.068688+00:00
-- url     : https://prove2.me/theorems/2d8a6542-a876-4f6e-b546-353569715611
-- title:
--   Actual controlled predictable Lévy jump L² energy remains finite under bounded stochastic localisation weights
-- statement:
--   For the original spectrally negative Levy X and an adapted full-Stieltjes dividend strategy D, the complete controlled strict-prejump negative-mark value-increment kernel J remains predictable and square-integrable with respect to the actual source Levy measure and any finite original predictable observation measure after multiplication by any jointly predictable-mark measurable weight K with absolute value at most one. This is the exact contraction step required to localise or discount compensated source-jump martingale integrands. It constructs neither a martingale nor an assumed stochastic chain rule.
-- source:
--   Direct finite-energy contraction of Proved original source controlled full negative-mark energy theorem 18dba881. Target bridge is the corrected canonical UBV core 429e17ca and BV core ef7e6c20; actual stopping predictability and source compensated martingale remain separate obligations.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_controlled_predictable_full_negative_mark_energy_finite

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_controlled_predictable_jump_energy_contraction
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
    (hμ : μ Set.univ < ⊤)
    (K : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hK : Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] K)
    (hKbound : ∀ p, |K p| ≤ 1) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let J : ((ℝ≥0 × Ω) × ℝ) → ℝ :=
      fun p => if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0
    Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] (fun p => K p * J p) ∧
      (∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in Iio (0 : ℝ),
          ENNReal.ofReal ((K (p, z) * J (p, z)) ^ 2) ∂X.ν ∂μ) < ⊤ := by
  sorry
