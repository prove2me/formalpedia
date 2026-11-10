-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf15_original_separated_annulus_compensated_covariance_zero
-- name    : AvramDividend.Classical.avram_mix_inf15_original_separated_annulus_compensated_covariance_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T13:51:44.607851+00:00
-- url     : https://prove2.me/theorems/9c325a05-7a98-483c-8d37-19518ea94cae
-- title:
--   Original physical compensated counts on separated negative mark annuli are orthogonal
-- statement:
--   For arbitrary ordered negative mark annuli n≤m≤p≤q, the original physical compensated counts on annuli (n,m] and (p,q] have integrable product and zero covariance, allowing empty gaps and degenerate endpoints. This extends accepted adjacent covariance through exact threecut source additivity and rate differences.
-- source:
--   Root-connected original mixed infinite-activity physical marked-jump L2 finite simple-mark isometry route from f5e6e083 through 5f12c023. Requires new Proved a13593f2, Proved 278f17b6, Proved 832d1bcb.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf15_original_adjacent_annulus_compensated_covariance_zero
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf13_original_threecut_annulus_real_additivity
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_annulus_levy_rate_difference

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_inf15_original_separated_annulus_compensated_covariance_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (n m p q : ℕ) (hnm : n ≤ m) (hmp : m ≤ p) (hpq : p ≤ q) :
    let B : ℕ → ℕ → Set ℝ := fun i j =>
      Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((j : ℝ) + 1)))
    let N : ℕ → ℕ → Ω → ℝ≥0∞ := fun i j ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B i j)
    let r : ℕ → ℕ → ℝ := fun i j =>
      ((T : ℝ≥0∞) * X.ν (B i j)).toReal
    let Y : ℕ → ℕ → Ω → ℝ := fun i j ω => (N i j ω).toReal - r i j
    Integrable (fun ω => Y n m ω * Y p q ω) P ∧
      (∫ ω, Y n m ω * Y p q ω ∂P) = 0 := by sorry
