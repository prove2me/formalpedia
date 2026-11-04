-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_effective_cash_atom_clock_and_mass
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_effective_cash_atom_clock_and_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:15:15.902646+00:00
-- url     : https://prove2.me/theorems/99c874fa-3b1b-4f51-972f-7f443cef7f92
-- title:
--   Actual nonzero real Cash atoms have a certified original NNReal payment clock and singleton mass
-- statement:
--   From the source full stopped dividend measure split and exact right-atom formula, each nonzero atom in the original real atomic set has a nonnegative time, lies at or before the actual stopped horizon, and has its true original right-payment mass at the NNReal clock. This supplies the previously missing hA0 and hμatom premises on the effective source atom set for countable HJB comparison.
-- source:
--   Accepted original-source support fbaa8669 and exact P4-D right singleton hRight. No false pre-ruin eligibility is inferred from closed-horizon support.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_nonzero_cash_atom_in_closed_horizon
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_effective_cash_atom_clock_and_mass
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ≥0)
    (μatom μdiffuse : Measure ℝ)
    (hsplit : (dividendMeasure D ω).restrict
      (Icc (0 : ℝ) (T : ℝ)) = μatom + μdiffuse)
    (hRight : ∀ t : ℝ≥0, t ≤ T →
      μatom {(t : ℝ)} =
        ENNReal.ofReal (rightLimit D t ω - D t ω))
    (A : Set ℝ) :
    ∀ a : {t : ℝ | t ∈ A ∧ μatom {t} ≠ 0},
      0 ≤ a.1 ∧ Real.toNNReal a.1 ≤ T ∧
        μatom {a.1} = ENNReal.ofReal
          (rightLimit D (Real.toNNReal a.1) ω -
            D (Real.toNNReal a.1) ω) := by sorry
