-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_shifted_centered_variance_exact
-- name    : AvramDividend.Classical.avram_p4_s3_interval_h_original_full_cutoff_shifted_centered_variance_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T16:51:03.033213+00:00
-- url     : https://prove2.me/theorems/53cd0ae1-720f-4c48-8ccb-65399d8962f1
-- title:
--   Exact original full negative-cutoff centred count L2 variance on any shifted physical window
-- statement:
--   For any original Lévy physical marked count N on (s,s+T] with negative marks below −1/(n+1), its centred real square is integrable and has exact expectation Tν(B), where B is the original cutoff. This closes genuine shifted-window unconditional variance through the proved zero-origin variance and the full actual-source count-law stationary real-moment transport, without another process or an extra factorial moment assumption.
-- source:
--   Uses already Proved zero-origin original full-cutoff centred variance 56c5b025 and the new original shifted real-moment theorem. The measurable test is z↦(z.toReal−r)^2 with r=Tν(B); the physical source NX is definitionally X's intrinsic marked count.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_e_original_cutoff_band_centered_variance_exact
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_intrinsic_marked_real_moment_stationary
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_interval_h_original_full_cutoff_shifted_centered_variance_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s T : ℝ≥0) (n : ℕ) :
    let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ B)
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => ((N ω).toReal - r) ^ 2) P ∧
    (∫ ω, ((N ω).toReal - r) ^ 2 ∂P) = r := by sorry
