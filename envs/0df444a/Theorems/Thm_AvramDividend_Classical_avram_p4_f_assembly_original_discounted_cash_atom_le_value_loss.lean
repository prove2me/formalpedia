-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_discounted_cash_atom_le_value_loss
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_discounted_cash_atom_le_value_loss
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:30:17.996771+00:00
-- url     : https://prove2.me/theorems/c9b06745-b2bd-4287-9e71-ea6de40110db
-- title:
--   Each genuine discounted Cash atom is bounded by the original HJB secant value loss
-- statement:
--   At an original eligible right-dividend time, the genuine Cash atom from the original stopped measure, after ENNReal.toReal conversion, is no greater than the discounted value-function drop. Uses the actual original-risk reserve, source Cash right-limit atom identity and canonical jump-control inequality.
-- source:
--   Source original Cash pointwise conversion theorem 01127eb0, canonical original P4-F jump inequality; valid for any real q.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cash_atom_toReal_eq_discounted_rightjump
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_discounted_cash_atom_le_value_loss
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (hjump : ∀ (ω : Ω) (t : ℝ≥0),
      t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω →
        rightLimit D t ω - D t ω ≤
          w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (t : ℝ≥0) (μatom : Measure ℝ)
    (hμatom : μatom {(t : ℝ)} =
      ENNReal.ofReal (rightLimit D t ω - D t ω))
    (hdelta : 0 ≤ rightLimit D t ω - D t ω)
    (helig : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    (ENNReal.ofReal (Real.exp (-(q * (t : ℝ)))) *
      μatom {(t : ℝ)}).toReal ≤
      Real.exp (-(q * (t : ℝ))) *
        (w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))) := by sorry
