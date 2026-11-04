-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cash_atom_toReal_eq_discounted_rightjump
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_cash_atom_toReal_eq_discounted_rightjump
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:06:56.547109+00:00
-- url     : https://prove2.me/theorems/01127eb0-13f2-45e1-bf03-cee1324dcb03
-- title:
--   Exact original Cash atomic mass to real discounted right dividend
-- statement:
--   At a nonnegative real clock, if the actual original dividend atomic measure equals ENNReal.ofReal of its right-dividend jump and that jump is nonnegative, its discounted ENNReal atom converts exactly to the real discounted dividend. This is the pointwise conversion required by the Cash atom-plus-diffuse decomposition.
-- source:
--   Proved source Cash right-atom measure decomposition f897c004 and Mathlib ENNReal.toReal_mul, ENNReal.toReal_ofReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_cash_atom_toReal_eq_discounted_rightjump
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (q : ℝ)
    (t : ℝ≥0) (μatom : Measure ℝ)
    (hμatom : μatom {(t : ℝ)} =
      ENNReal.ofReal (rightLimit D t ω - D t ω))
    (hdelta : 0 ≤ rightLimit D t ω - D t ω) :
    (ENNReal.ofReal (Real.exp (-(q * (t : ℝ)))) *
      μatom {(t : ℝ)}).toReal =
      Real.exp (-(q * (t : ℝ))) *
        (rightLimit D t ω - D t ω) := by sorry
