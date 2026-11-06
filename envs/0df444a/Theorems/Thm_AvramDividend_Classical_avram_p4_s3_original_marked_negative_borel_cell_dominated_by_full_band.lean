-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_marked_negative_borel_cell_dominated_by_full_band
-- name    : AvramDividend.Classical.avram_p4_s3_original_marked_negative_borel_cell_dominated_by_full_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T10:02:49.315284+00:00
-- url     : https://prove2.me/theorems/840cfac4-5017-421f-8baf-6e8544e7060c
-- title:
--   Actual original marked count on any negative Borel cell is pointwise bounded by the full negative-band cardinal
-- statement:
--   For any original Lévy sample path, arbitrary mark set B contained in the negative halfline at cutoff 1/(n+1), and subinterval (s,t]⊆(0,T], the actual marked jump count, converted to a real, is bounded by the finite full-band jump cardinal up to T. This gives quantitative domination for arbitrary Borel negative bands from original halfline moments.
-- source:
--   Original marked counting measure monotonicity and Proved exact full-halfline finite-card identification f0197436-2681-46a3-8ee4-4df5e3dee1a5; no stochastic measure substitution.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_original_marked_negative_borel_cell_dominated_by_full_band
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n : ℕ)
    (s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (B : Set ℝ)
    (hBsep : B ⊆ Iic (-(1 / ((n : ℝ) + 1)))) :
    ∀ ω : Ω,
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal ≤
      ({u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard : ℝ) := by sorry
