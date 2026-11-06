-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_physical_weighted_negative_cell_explicit_L2_energy_budget
-- name    : AvramDividend.Classical.avram_p4_s3_original_physical_weighted_negative_cell_explicit_L2_energy_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:26:15.034327+00:00
-- url     : https://prove2.me/theorems/eda7e9e1-b9e9-44d4-ac17-ba355985e035
-- title:
--   Original bounded predictable negative-mark cell has an explicit physical L2 energy budget
-- statement:
--   For the actual marked jump count of a spectrally negative Levy process on a negative measurable subband B and a bounded predictable time-s weight H, the compensated cell has quadratic energy no greater than L² times the explicit full-band budget 2(R²+R)+2r². The result retains the physical original jump measure and does not assume Poisson isometry, independent copy or equality in law.
-- source:
--   Source-exact original marked count and pinned Mathlib integral_mono_ae, from P4-S3 weighted finite-band L² helper 11dd20c2 and explicit centred-count L² budget 8feb9a50.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_original_physical_weighted_negative_cell_explicit_L2_energy_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (cut : ℕ)
    (s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (ε : ℝ) (hε : 0 < ε) (B : Set ℝ)
    (hB : MeasurableSet B) (hBand : B ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : B ⊆ Iic (-(1 / ((cut : ℝ) + 1))))
    (H : Ω → ℝ) (hH : StronglyMeasurable[𝓕 s] H)
    (hHL2 : MemLp H 2 P)
    (L : ℝ) (hBound : ∀ ω, |H ω| ≤ L) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)
    let r : ℝ :=
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
    let R : ℝ :=
      ((T : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal
    (∫ ω, (H ω * ((N ω).toReal - r)) ^ 2 ∂P) ≤
      L ^ 2 * (2 * (R ^ 2 + R) + 2 * r ^ 2) := by sorry
