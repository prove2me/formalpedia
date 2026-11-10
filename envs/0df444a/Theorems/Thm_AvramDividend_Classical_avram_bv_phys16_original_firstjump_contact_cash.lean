-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_phys16_original_firstjump_contact_cash
-- name    : AvramDividend.Classical.avram_bv_phys16_original_firstjump_contact_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T12:56:56.060892+00:00
-- url     : https://prove2.me/theorems/ec4db783-067b-4e86-b6c3-ad11eacbb390
-- title:
--   Original pre-first-negative-jump zero-reserve physical cell has exact weighted drift cash
-- statement:
--   On the actual finite-activity BV source and original admissible dividends, a half-open physical cell strictly before the first actual negative jump has no source jumps. If the post-right-payment controlled reserve is zero on the cell, its arbitrary nonnegative weighted Stieltjes dividend cash equals original drift-weighted Lebesgue cash. One common almost-sure event works for all cells. The strict comparison excludes the final first-negative-jump atom, which must be handled separately. From Proved a2c33db6 and bc78efba, without a global drift L1 assumption.
-- source:
--   Source-exact physical-cell zero-contact subcase of 2bc848f9 and 4f605d76. Original X,D, filtration, strictly pre-first-jump chronology.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_all_pathwise_restart_zero_weighted_cash_no_survival
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_before_first_negative_jump_source_increments_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_phys16_original_firstjump_contact_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) (hDrift : 0 ≤ X.drift)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ≥0) (hH : 0 < H) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t → t ≤ H →
      (t : WithTop ℝ≥0) <
        (⨅ v : ℝ≥0,
          if 0 < v ∧ X.X v ω -
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) v < 0
          then (v : WithTop ℝ≥0) else ⊤) →
      (∀ v : ℝ≥0, s ≤ v → v ≤ t →
        riskProcess X x D v ω -
          (rightLimit D v ω - D v ω) = 0) →
      ∀ f : ℝ → ℝ≥0∞,
        (∫⁻ r in Ioc (s : ℝ) (t : ℝ), f r
          ∂(dividendMeasure D ω)) =
        (∫⁻ r in Ioc (s : ℝ) (t : ℝ), f r
          ∂((ENNReal.ofReal X.drift) • volume)) := by sorry
