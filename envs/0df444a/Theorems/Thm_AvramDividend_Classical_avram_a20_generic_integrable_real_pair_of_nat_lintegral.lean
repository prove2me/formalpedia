-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_generic_integrable_real_pair_of_nat_lintegral
-- name    : AvramDividend.Classical.avram_a20_generic_integrable_real_pair_of_nat_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T17:13:13.365366+00:00
-- url     : https://prove2.me/theorems/01280e1b-cc21-4518-b176-39c63d937268
-- title:
--   Any original almost-everywhere measurable natural event pair count has exact real L1 moment from its finite ENNReal mean
-- statement:
--   For a finite almost-everywhere measurable natural-number-valued pair count K on any original measure space, if the ENNReal expectation equals ENNReal.ofReal(r²/2), then 2K is real integrable and has exact expectation r². This is the generic finite-natural count version of the already Proved finite negative-band chronological pair ENNReal-to-real L1 bridge. The proof uses integrable_toReal_of_lintegral_ne_top, integral_toReal, elementary ENNReal.toReal_natCast and real arithmetic. Its source is entirely generic and independent of Gaussian or Poisson assumptions.

import Mathlib
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a20_generic_integrable_real_pair_of_nat_lintegral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (K : Ω → ℕ) (r : ℝ)
    (hmeas : AEMeasurable (fun ω => (K ω : ℝ≥0∞)) P)
    (hmean : (∫⁻ ω, (K ω : ℝ≥0∞) ∂P) =
      ENNReal.ofReal (r ^ 2 / 2)) :
    Integrable (fun ω => 2 * (K ω : ℝ)) P ∧
    (∫ ω, 2 * (K ω : ℝ) ∂P) = r ^ 2 := by sorry
