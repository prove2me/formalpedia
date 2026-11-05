-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f2_original_band_count_factorial_moment_exact
-- name    : AvramDividend.Classical.avram_p4_f2_original_band_count_factorial_moment_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:39:01.396203+00:00
-- url     : https://prove2.me/theorems/0a13392f-85cb-4eda-8293-758dc8d8a2a7
-- title:
--   Exact original Lévy negative-band count second factorial moment
-- statement:
--   For the literal original spectrally negative Lévy jump count in a fixed finite negative-jump band over (0,T], its second factorial moment is integrable and equals the square of the physical intensity T times Lévy measure. Proof transports the original chronological-pair expectation using the proven pathwise factorial-pair identity.
-- source:
--   Proved original physical chronological pair expectation d938e9a5-b97c-409b-bffb-bfef53c53ef0 and pathwise factorial pairing 074f945f-26c2-4404-8c57-4116b63d7eef; source-faithful original process, no auxiliary Y.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_chronological_pair_mean_exact
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_negative_band_real_factorial_pair

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f2_original_band_count_factorial_moment_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1))))
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => (N ω).toReal * ((N ω).toReal - 1)) P ∧
    (∫ ω, (N ω).toReal * ((N ω).toReal - 1) ∂P) = r ^ 2 := by sorry
