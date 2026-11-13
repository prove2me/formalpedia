-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a42_positive_only_spatial_cell_aestronglyMeasurable
-- name    : AvramDividend.Classical.avram_ga_a42_positive_only_spatial_cell_aestronglyMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T12:57:50.414992+00:00
-- url     : https://prove2.me/theorems/078062aa-3e6f-49e0-8f44-09f178cb3fe7
-- title:
--   Measurable original physical spatial cell from positive active and zero inactive alternatives
-- statement:
--   If the prepayment and postpayment reserve coordinates and two discounts are measurable, and almost every cell is either inactive (discount unchanged and pre/postpayment reserves equal) or active with both reserves positive, then the single discounted spatial difference E1*(w(Z)-w(Y)) is almost everywhere strongly measurable for any value function continuous on the positive halfline. Obtain the result by applying the Proved gledger76 measurable-source-sum theorem to a one-cell sum and separately to its discount-only part, then subtract. This is the exact measurable-cell mechanism required to close a41a for the original Gaussian terminal positive cell.
-- source:
--   Original a41a ba766c92-bfb5-492b-a445-9cc908da7bce; Proved gledger76 0f5b5d56.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger76_positive_only_value_masked_physical_source_measurable
open AvramDividend.Classical MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_ga_a42_positive_only_spatial_cell_aestronglyMeasurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (w : ℝ → ℝ) (hw : ContinuousOn w (Set.Ioi (0 : ℝ)))
    (E0 E1 Y Z : Ω → ℝ)
    (hE0 : Measurable E0) (hE1 : Measurable E1)
    (hY : Measurable Y) (hZ : Measurable Z)
    (hcell : ∀ᵐ ω ∂ P,
      (E1 ω = E0 ω ∧ Z ω = Y ω) ∨
      (0 < Y ω ∧ 0 < Z ω)) :
    AEStronglyMeasurable
      (fun ω => E1 ω * (w (Z ω) - w (Y ω))) P := by sorry
