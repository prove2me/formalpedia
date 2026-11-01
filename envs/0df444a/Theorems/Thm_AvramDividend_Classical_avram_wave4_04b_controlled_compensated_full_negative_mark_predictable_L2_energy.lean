-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_compensated_full_negative_mark_predictable_L2_energy
-- name    : AvramDividend.Classical.avram_wave4_04b_controlled_compensated_full_negative_mark_predictable_L2_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T20:29:08.552762+00:00
-- url     : https://prove2.me/theorems/67a347f4-b864-4fc8-9dec-0d09777d91dd
-- title:
--   Genuine controlled compensated negative-mark kernel is predictable and has finite nested Lévy L² energy
-- statement:
--   On the original adapted spectrally negative Lévy source with arbitrary admissible full-variation dividend strategy, the predictable strict pre-jump controlled reserve masked to any compact strictly interior band yields a measurable compensated negative-mark integrand H(t,ω,z)=w(Y+z)-w(Y)-z w'(Y)1_{-1<z<0}, zero off-band, with finite nested squared integral under any finite observation measure on the original right-continuous predictable space and the actual source Lévy mark measure. All negative marks crossing ruin are retained; no finite first absolute jump moment is assumed. This establishes the analytic predictable-L2 prerequisite and does not assert a source-X Poisson random measure or stochastic martingale.
-- source:
--   Proved actual controlled full negative-mark energy 18dba881, compact predictable derivative energy bcd9edf0, and the new original-source compensated quadratic envelope c02ee5a4. Source ν-integrable Lévy min-squared bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_controlled_predictable_full_negative_mark_energy_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_prejump_gradient_compact_band_L2_energy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_original_full_negative_mark_compensated_kernel_uniform_energy_envelope

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_controlled_compensated_full_negative_mark_predictable_L2_energy
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
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] H ∧
      (∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in Iio (0 : ℝ),
          ENNReal.ofReal ((H (p, z)) ^ 2) ∂X.ν ∂μ) < ⊤ := by
  sorry
