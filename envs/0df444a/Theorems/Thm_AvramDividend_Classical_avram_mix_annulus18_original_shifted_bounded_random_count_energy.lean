-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_annulus18_original_shifted_bounded_random_count_energy
-- name    : AvramDividend.Classical.avram_mix_annulus18_original_shifted_bounded_random_count_energy
-- status  : Open
-- author  : @WillR
-- created : 2026-11-09T23:29:38.581291+00:00
-- url     : https://prove2.me/theorems/680f4d4c-e205-4c5d-b44d-f64d688d24ac
-- title:
--   Original shifted physical annulus bounded random coefficient L2 energy
-- statement:
--   On every original physical shifted annulus time window, a bounded random multiplier of the compensated jump count has integrable square and expected square controlled by the squared multiplier bound times the exact physical Lévy variance. The proof uses the authoritative original shifted variance and a pointwise square domination, without replacing the process or requiring artificial independence of the multiplier.
-- source:
--   Root-connected original mixed infinite-activity stopped jump source 065e7a28; generalises Proved 492f5cd1 origin bound via shifted physical variance 99d7b9e5.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_annulus16_original_shifted_physical_variance_exact
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_annulus18_original_shifted_bounded_random_count_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s T : ℝ≥0)
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
        (Ioc s (s + T) ×ˢ B)
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    AEStronglyMeasurable
        (fun ω => (H ω * ((N ω).toReal - r)) ^ 2) P →
      Integrable (fun ω => (H ω * ((N ω).toReal - r)) ^ 2) P ∧
      (∫ ω, (H ω * ((N ω).toReal - r)) ^ 2 ∂P) ≤ L ^ 2 * r := by sorry
