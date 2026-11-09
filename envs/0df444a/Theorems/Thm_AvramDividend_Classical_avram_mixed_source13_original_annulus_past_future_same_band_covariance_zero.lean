-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_annulus_past_future_same_band_covariance_zero
-- name    : AvramDividend.Classical.avram_mixed_source13_original_annulus_past_future_same_band_covariance_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T01:18:50.00553+00:00
-- url     : https://prove2.me/theorems/25c87c2d-94ed-4f38-9e4f-28cd4b0bc264
-- title:
--   Original same negative annulus has orthogonal past and future physical counts
-- statement:
--   For the original spectrally negative Levy process, in its original sample space, probability and filtration, the past physical annulus count on (0,s] and the future same-annulus count on (s,t] have an integrable centred real product with zero mean, with true annulus compensator rates. This imports Proved c17e6a0d and the necessary original finite cutoff Levy-rate identification. It is the off-diagonal input to exact annulus factorial moment 6ea0212e.
-- source:
--   MIX-SOURCE13 physical annulus orthogonality; no independent auxiliary process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mixed_source13_original_annulus_past_future_same_band_covariance_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (n m : ℕ) (hnm : n ≤ m) :
    let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let A : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 s ×ˢ B)
    let F : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)
    let r : ℝ := ((s : ℝ≥0∞) * X.ν B).toReal
    let q : ℝ := (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => ((A ω).toReal - r) * ((F ω).toReal - q)) P ∧
    (∫ ω, ((A ω).toReal - r) * ((F ω).toReal - q) ∂P) = 0 := by sorry
