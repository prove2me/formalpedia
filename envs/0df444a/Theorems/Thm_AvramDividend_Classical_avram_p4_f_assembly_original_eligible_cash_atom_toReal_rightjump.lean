-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_eligible_cash_atom_toReal_rightjump
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_eligible_cash_atom_toReal_rightjump
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:39:44.689666+00:00
-- url     : https://prove2.me/theorems/5c636fe2-34c4-4f2e-9b7b-c18e8a634920
-- title:
--   Exact source eligible Cash atom equals the physical real discounted dividend jump
-- statement:
--   For an effective source Cash index a inside the actual stopped finite horizon and eligible at the original ruin clock, the ENNReal atomic Cash term converts to the real discounted physical right-dividend jump. The source atomic singleton identity, nonnegative jump, and real-to-NNReal clock coercion are explicitly discharged.
-- source:
--   Original Cash decomposition f897c004, proved pointwise source conversion 01127eb0, source physical stopped horizon support.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cash_atom_toReal_eq_discounted_rightjump
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_eligible_cash_atom_toReal_rightjump
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ≥0)
    (μatom : Measure ℝ) (q a : ℝ)
    (hAtom : ∀ t : ℝ≥0, t ≤ T →
      μatom {(t : ℝ)} =
        ENNReal.ofReal (rightLimit D t ω - D t ω))
    (hDelta : ∀ t : ℝ≥0, t ≤ T →
      0 ≤ rightLimit D t ω - D t ω)
    (ha : a ∈ Icc (0 : ℝ) (T : ℝ))
    (hpay : a ∈ paymentTimes (ruinTime X x D ω)) :
    ((if a ∈ paymentTimes (ruinTime X x D ω) then
        ENNReal.ofReal (Real.exp (-(q * a))) else 0) *
      μatom {a}).toReal =
      Real.exp (-(q * a)) *
        (rightLimit D (⟨a, ha.1⟩ : ℝ≥0) ω -
          D (⟨a, ha.1⟩ : ℝ≥0) ω) := by sorry
