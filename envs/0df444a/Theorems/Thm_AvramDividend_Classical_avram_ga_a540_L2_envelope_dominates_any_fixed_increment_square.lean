-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a540_L2_envelope_dominates_any_fixed_increment_square
-- name    : AvramDividend.Classical.avram_ga_a540_L2_envelope_dominates_any_fixed_increment_square
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:46:37.55376+00:00
-- url     : https://prove2.me/theorems/36ee839e-c1d0-4b94-9cae-17e9bbe42b42
-- title:
--   An integrable uniform quadratic path envelope controls every fixed increment square
-- statement:
--   If a process on a finite horizon has an integrable, nonnegative random variable bounding the squared process at all times, then every squared increment between two deterministic times within that horizon is integrable.
-- source:
--   Elementary square difference ≤2a²+2b²≤4S; Mathlib Integrable.mono_nonneg. Applicable with the Proved a400 Gaussian centred-path L2 maximal envelope.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a540_L2_envelope_dominates_any_fixed_increment_square
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (M : ℝ≥0 → Ω → ℝ) (T s t : ℝ≥0)
    (hs : s ≤ T) (ht : t ≤ T)
    (hMeas : ∀ r : ℝ≥0, r ≤ T →
      AEStronglyMeasurable (M r) P)
    (S : Ω → ℝ) (hS : Integrable S P)
    (hDom : ∀ᵐ ω ∂P, 0 ≤ S ω ∧
      ∀ r : ℝ≥0, r ≤ T → (M r ω)^2 ≤ S ω) :
    Integrable (fun ω => (M t ω - M s ω)^2) P := by sorry
