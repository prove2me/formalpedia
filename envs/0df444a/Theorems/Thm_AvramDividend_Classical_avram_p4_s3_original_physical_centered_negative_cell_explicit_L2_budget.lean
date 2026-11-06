-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_physical_centered_negative_cell_explicit_L2_budget
-- name    : AvramDividend.Classical.avram_p4_s3_original_physical_centered_negative_cell_explicit_L2_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:02:00.253843+00:00
-- url     : https://prove2.me/theorems/8feb9a50-25d9-409b-b5c3-e23014505d3a
-- title:
--   Original physical negative Borel cell compensated variance bounded explicitly by full-band second moments
-- statement:
--   For actual original Lévy jumps in a negative Borel subband within a bounded horizon T, the compensated count has finite second moment, bounded by 2(R²+R)+2r² with R=T ν(full threshold band) and r=(t-s)ν(B), using only the source full-band moment budget. No independent factorial moment or abstract Poisson equality-in-law assumption is introduced.
-- source:
--   P4-S3 original source cell second moment 367c2c5e, original subband centered MemLp2 963870c8, square inequality and monotonicity of Lebesgue integral.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_original_physical_centered_negative_cell_explicit_L2_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (cut : ℕ)
    (s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hCut : B ⊆ Iic (-(1 / ((cut : ℝ) + 1)))) :
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
    Integrable (fun ω => ((N ω).toReal - r) ^ 2) P ∧
    (∫ ω, ((N ω).toReal - r) ^ 2 ∂P) ≤
      2 * (R ^ 2 + R) + 2 * r ^ 2 := by sorry
