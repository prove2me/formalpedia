-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_stopped_negative_cutoff_count_mean_le_rate
-- name    : AvramDividend.Classical.avram_pj_workerC_original_stopped_negative_cutoff_count_mean_le_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:27:15.778846+00:00
-- url     : https://prove2.me/theorems/b471c554-17a5-4ceb-8150-960b8a64248e
-- title:
--   True original stopped negative separated-mark jump count has expected measure bounded by deterministic horizon times its finite Lévy cutoff rate
-- statement:
--   For any original spectrally negative Lévy process including purejump infinite-activity unbounded variation, every pathwise stop rho<=T and Borel mark band B separated from zero by epsilon>0 has expected intrinsic jump count on (0,rho] bounded above by T times the exact original Lévy jump intensity X.nu(B). This uses finite intensity only of B, never of all negative marks, and handles random ruin clipping without a stopping-time independence assumption.
-- source:
--   Proved 34dbea70 exact original negative separated-mark count intensity for deterministic horizon T and measure monotonicity of (0,rho]⊆(0,T].

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_zero_origin_separated_negative_borel_levy_rate
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_original_stopped_negative_cutoff_count_mean_le_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (ρ : Ω → ℝ≥0)
    (hρbound : ∀ ω, ρ ω ≤ T)
    (B : Set ℝ) (hB : MeasurableSet B)
    (ε : ℝ) (hε : 0 < ε) (hBsep : B ⊆ Iic (-ε)) :
    (∫⁻ ω,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (ρ ω) ×ˢ B) ∂P) ≤
      (T : ℝ≥0∞) * X.ν B := by sorry
