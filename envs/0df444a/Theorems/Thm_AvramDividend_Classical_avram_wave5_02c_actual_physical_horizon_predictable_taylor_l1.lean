-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_02c_actual_physical_horizon_predictable_taylor_l1
-- name    : AvramDividend.Classical.avram_wave5_02c_actual_physical_horizon_predictable_taylor_l1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:04:48.614064+00:00
-- url     : https://prove2.me/theorems/8cd8dc4a-cfac-4542-b4f8-df8a6dfa6de5
-- title:
--   Literal finite-horizon physical predictable intensity supports actual ruin-stopped Taylor L1
-- statement:
--   For the unchanged original spectrally negative Levy source and any deterministic finite horizon T, choose the finite right-continuous predictable measure agreeing with actual horizon-truncated Lebesgue time times original probability on every predictable set. Against its genuine negative-mark Levy intensity the inclusively ruin-stopped controlled nonlinear C2 Taylor reward is L1 integrable. No whole-infinite-horizon integrability, Poisson replacement, or source rectangle law is assumed.
-- source:
--   Proved finite-horizon predictable time-probability measure 16857b34, Chat03 actual stopped negative-mark Taylor L1 0e0663b1, and negative Lévy s-finiteness.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_source_finite_horizon_predictable_lintegral_eq_time_probability
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_02c_actual_physical_horizon_predictable_taylor_l1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (T : ℝ≥0) :
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
        μ A = ((((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
      (let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
       let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
         (if Y p.1 ∈ Icc (u + δ) v then
           w (Y p.1 + p.2) - w (Y p.1) else 0) -
         (if -1 < p.2 then
           p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
           else 0)
       let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
         (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
       letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
       Integrable HS (μ.prod (X.ν.restrict (Iio (0 : ℝ))))) := by sorry
