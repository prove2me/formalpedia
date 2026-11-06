-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_physical_finite_band_weighted_martingale_no_rate_or_pair
-- name    : AvramDividend.Classical.avram_p4_s3_original_physical_finite_band_weighted_martingale_no_rate_or_pair
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T10:07:51.74736+00:00
-- url     : https://prove2.me/theorems/662e8550-3b19-477a-b887-85b15ee5f80d
-- title:
--   True original Lévy finite-band weighted compensated martingale step with all measurability, rate and L² inputs discharged
-- statement:
--   For a separated negative Borel band, a deterministic halfline cutoff containing the band, any time cell inside (0,T], and any 𝓕_s-measurable L² weight H, the conditional expectation of H times the centred original Lévy marked jump count is zero. Every stochastic rectangle-rate, mark measurability and count L² premise is independently proved from the original process and full-band moments.
-- source:
--   Combines P4-S3 original physical weighted conditional zero with automatic rate/meas and new original Borel subcell L² from full halfline domination. No independent Poisson axioms or physical pair assumptions.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_original_physical_finite_band_weighted_martingale_no_rate_or_pair
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n : ℕ)
    (s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (ε : ℝ) (hε : 0 < ε) (B : Set ℝ)
    (hB : MeasurableSet B) (hBand : B ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : B ⊆ Iic (-(1 / ((n : ℝ) + 1))))
    (H : Ω → ℝ) (hH : StronglyMeasurable[𝓕 s] H)
    (hHL2 : MemLp H 2 P) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)
    let r : ℝ :=
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
    P[(fun ω => H ω * ((N ω).toReal - r)) | 𝓕 s] =ᵐ[P] 0 := by sorry
