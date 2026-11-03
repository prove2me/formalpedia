-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_generator_signed_negative_mark_cutoff_predictable
-- name    : AvramDividend.Classical.avram_wave7_07_original_generator_signed_negative_mark_cutoff_predictable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:24:43.568677+00:00
-- url     : https://prove2.me/theorems/79c84e83-b740-4c15-b6ee-081b151a5c0c
-- title:
--   Actual stopped C² negative Lévy generator cutoff drift is predictable for every measurable negative-mark set
-- statement:
--   For the actual spectrally negative Lévy source X, actual admissible filtration and original controlled prepayment reserve, prove that integration of the ruin-stopped C2 generator Taylor kernel over any measurable subset of negative Lévy marks yields a predictable signed real drift. This discharges the per-cutoff measurability hypothesis of the accepted true-clock shrinking-tail theorem. The proof uses the original-source predictable joint Taylor kernel and its exact markwise generator identity, with no replacement Poisson or Brownian sample space.
-- source:
--   Wave 7 Chat 07 source-specific C2 negative-mark cutoff predictability, deriving from accepted Wave5 source joint predictable Taylor kernel and exact generator-integrand equality. Intended as an analytic interface for eeeff969 true-clock weighted generator tail.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_source_generator_jump_drift_integral_eq
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_07_original_generator_signed_negative_mark_cutoff_predictable
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
    (B : Set ℝ) (hBm : MeasurableSet B)
    (hBneg : B ⊆ Iio (0 : ℝ)) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    Measurable[𝓕.rightCont.predictable] (fun p : ℝ≥0 × Ω =>
      ∫ z in B, JG (p,z) ∂X.ν) := by sorry
