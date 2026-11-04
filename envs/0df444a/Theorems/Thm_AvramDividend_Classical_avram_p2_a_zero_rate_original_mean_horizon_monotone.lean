-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_mean_horizon_monotone
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_original_mean_horizon_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:11:42.470888+00:00
-- url     : https://prove2.me/theorems/84da885d-6d68-40f2-b293-342ce20294bc
-- title:
--   Original marked Lévy jump-count mean is monotone in physical horizon
-- statement:
--   For the genuine original spectrally negative Levy process on Ω/P, prove its intrinsic nonnegative expected marked jump count on (0,s] cannot exceed that on (0,t] whenever s≤t, for an arbitrary mark set B, using only measure monotonicity of the actual source counting measure. No Lévy intensity identification is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_original_mean_horizon_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (B : Set ℝ) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 s ×ˢ B) ∂P) ≤
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 t ×ˢ B) ∂P) := by sorry
