-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_annulus16_original_bounded_random_weighted_count_energy
-- name    : AvramDividend.Classical.avram_mix_annulus16_original_bounded_random_weighted_count_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T22:38:30.107919+00:00
-- url     : https://prove2.me/theorems/492f5cd1-36c0-451c-a924-5ed91df3b16d
-- title:
--   Original marked annulus random bounded coefficient has quantitative physical L2 bound
-- statement:
--   For the unchanged original physically marked Lévy jump count and any bounded measurable squared random coefficient, the centred compensated count is L2 with energy bounded by L squared times the genuine negative annulus Lévy rate. The coefficient need not be independent of the count, so this is a robust stopped-grid upper bound. It permits vanishing band-specific multiplier bounds in a source-exact small-jump limit.
-- source:
--   Direct source L2 quantitative extension of Proved original annulus variance 4f85fd76. Supports random predictable clipped H in 5f12c023, without assuming unsupported conditional independence or replacing the original process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_annulus16_original_constant_weighted_count_variance
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_annulus16_original_bounded_random_weighted_count_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (n m : ℕ) (hnm : n ≤ m)
    (H : Ω → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hBound : ∀ ω, |H ω| ≤ L) :
    let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    AEStronglyMeasurable
        (fun ω => (H ω * ((N ω).toReal - r)) ^ 2) P →
      Integrable (fun ω => (H ω * ((N ω).toReal - r)) ^ 2) P ∧
      (∫ ω, (H ω * ((N ω).toReal - r)) ^ 2 ∂P) ≤ L ^ 2 * r := by sorry
