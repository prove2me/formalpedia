-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_centered_finite_band_count_L1_mean_zero_auto
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_centered_finite_band_count_L1_mean_zero_auto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:39:30.529042+00:00
-- url     : https://prove2.me/theorems/40d4af83-ff28-42fb-a78b-410bd0f25490
-- title:
--   Same-original-process intrinsic marked count is integrable and exactly mean zero after source ν centring
-- statement:
--   For the actual original spectrally negative Levy path, the intrinsic negative-band marked count is automatically L1 on the original probability space and has exact expected source intensity Tν(B). Subtraction of this deterministic source intensity produces an integrable mean-zero count. No additional conditional expectation, independent Poisson proxy, or integrability hypothesis is introduced.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cutoff_marked_count_L1_auto
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cutoff_marked_count_real_mean_auto
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_centered_finite_band_count_L1_mean_zero_auto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    let J : Ω → ℝ := fun ω =>
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1))))).toReal
    let r : ℝ :=
      (((T : ℝ≥0) : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => J ω - r) P ∧
      (∫ ω, J ω - r ∂P) = 0 := by sorry
