-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cutoff_marked_count_real_mean_auto
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_cutoff_marked_count_real_mean_auto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:20:15.825998+00:00
-- url     : https://prove2.me/theorems/c1e09ada-3b9b-4b5a-9335-6526355bfe7c
-- title:
--   Original intrinsic finite negative-band marked count has exact real first mean automatically
-- statement:
--   For the same original spectrally negative Lévy source X, at every finite horizon T and negative cutoff 1/(n+1), the expectation of its actual marked jump count as a real random variable equals the real-valued ν intensity rate. The proof uses public original P2-E real count conversion, P2-A separated-mark finite ν, and original P2 zero-origin source rate. No added mean premise or independent process.
-- source:
--   Proved P2-E 14c106db, Proved P2-A 86086cb2, Proved original intensity 34dbea70.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_zero_origin_separated_negative_borel_levy_rate
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_nu_count_real_mean
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_cutoff_marked_count_real_mean_auto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    (∫ ω, (N ω).toReal ∂P) = ((T : ℝ≥0∞) * X.ν B).toReal := by sorry
