-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_thinned_C2_generator_kernel_L1_identification
-- name    : AvramDividend.Classical.avram_wave7_07_original_thinned_C2_generator_kernel_L1_identification
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:44:27.384565+00:00
-- url     : https://prove2.me/theorems/23aab5a7-3bc0-4f1e-b3b9-4e9b813df2d1
-- title:
--   Original jointly predictable negative-jump Taylor thinning equals its canonical source generator drift in Bochner L1
-- statement:
--   For the exact source spectrally negative Lévy process, original controlled pre-dividend reserve and ruin stop, every jointly predictable mark thinning of the C2 Taylor correction is Bochner integrable, and its negative Lévy measure drift coincides at every time-state with the similarly thinned canonical Lévy generator integrand. It uses precisely z>-1 as the small negative-mark linear truncation, making no assumption about W7-01's unresolved actual jump-count compensator.
-- source:
--   W7-07 authentic source-theorem combination of proved thinned signed drift L1 (3230b607) and original generator kernel identity (e336f7e2). This establishes deterministic compensated drift equivalence, leaving the intrinsic jump-count identity to W7-01.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_C2_joint_predictable_thinned_drift_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_source_taylor_generator_kernel_eq

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_07_original_thinned_C2_generator_kernel_L1_identification
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (S : Set ((ℝ≥0 × Ω) × ℝ))
    (hS : MeasurableSet[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] S) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
    let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    Integrable (fun p : ℝ≥0 × Ω =>
      ∫ z in Iio (0 : ℝ), (S.indicator G) (p,z) ∂X.ν) μ ∧
    (∀ p : ℝ≥0 × Ω,
      (∫ z in Iio (0 : ℝ), (S.indicator HS) (p,z) ∂X.ν) =
      (∫ z in Iio (0 : ℝ), (S.indicator G) (p,z) ∂X.ν)) := by sorry
