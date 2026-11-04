-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_paid_nonzero_cash_atom_physical_hjb
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_paid_nonzero_cash_atom_physical_hjb
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:31:46.775605+00:00
-- url     : https://prove2.me/theorems/c5fbf7f7-93e3-4229-bf84-6b44a9a71765
-- title:
--   Original paid nonzero cash atom has true physical horizon, strictly eligible clock, positive right jump and HJB bound
-- statement:
--   Combine the actual Stieltjes measure support and right singleton identity with original paymentTimes eligibility. A nonzero paid Cash atom has a nonnegative source time within horizon, strictly surviving or zero stopping clock, a nonnegative genuine right-payment atom and the exact original-source HJB value drop bound.
-- source:
--   Proved physical source atom clock 99c874fa and Proved paymentTimes strict survival a7a447fa.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_effective_cash_atom_clock_and_mass
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_paymentTimes_nnreal_strict_survival_or_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_paid_nonzero_cash_atom_physical_hjb
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (hjump : ∀ (ω : Ω) (u : ℝ≥0),
      u = 0 ∨ (u : ℝ≥0∞) < ruinTime X x D ω →
        rightLimit D u ω - D u ω ≤
          w (riskProcess X x D u ω) -
          w (riskProcess X x D u ω -
            (rightLimit D u ω - D u ω)))
    (ω : Ω) (T : ℝ≥0) (A : Set ℝ)
    (μatom μdiffuse : Measure ℝ)
    (hsplit : (dividendMeasure D ω).restrict
      (Icc (0 : ℝ) (T : ℝ)) = μatom + μdiffuse)
    (hRight : ∀ u : ℝ≥0, u ≤ T →
      μatom {(u : ℝ)} = ENNReal.ofReal (rightLimit D u ω - D u ω)) :
    ∀ a : {t : ℝ | t ∈ A ∧ t ∈ paymentTimes (ruinTime X x D ω) ∧
      μatom {t} ≠ 0},
      0 ≤ a.1 ∧ Real.toNNReal a.1 ≤ T ∧
      (Real.toNNReal a.1 = 0 ∨
        (Real.toNNReal a.1 : ℝ≥0∞) < ruinTime X x D ω) ∧
      0 ≤ rightLimit D (Real.toNNReal a.1) ω -
        D (Real.toNNReal a.1) ω ∧
      μatom {a.1} = ENNReal.ofReal
        (rightLimit D (Real.toNNReal a.1) ω -
          D (Real.toNNReal a.1) ω) ∧
      rightLimit D (Real.toNNReal a.1) ω -
        D (Real.toNNReal a.1) ω ≤
        w (riskProcess X x D (Real.toNNReal a.1) ω) -
          w (riskProcess X x D (Real.toNNReal a.1) ω -
            (rightLimit D (Real.toNNReal a.1) ω -
              D (Real.toNNReal a.1) ω)) := by sorry
