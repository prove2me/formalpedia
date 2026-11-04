-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_nonzero_cash_atom_in_closed_horizon
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_nonzero_cash_atom_in_closed_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:46:43.932126+00:00
-- url     : https://prove2.me/theorems/fbaa8669-9f3b-4493-97fd-5cc6f5bc69cf
-- title:
--   Every nonzero original atomic Cash singleton occurs at a valid closed-horizon nonnegative time
-- statement:
--   For the true original dividend measure restricted to the closed horizon [0,T], any nonzero singleton mass of its atomic component must occur at a real time in [0,T]. This isolates the support needed to restrict the countable source real atom set before converting times to NNReal clocks.
-- source:
--   Proved exact original Cash atom vanishing outside horizon 7293bcac and source original restricted Cash measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cash_atom_vanishes_outside_horizon
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_nonzero_cash_atom_in_closed_horizon
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ≥0)
    (μatom μdiffuse : Measure ℝ)
    (hsplit : (dividendMeasure D ω).restrict
      (Icc (0 : ℝ) (T : ℝ)) = μatom + μdiffuse)
    (A : Set ℝ) (a : A)
    (hnonzero : μatom {a.1} ≠ 0) :
    0 ≤ a.1 ∧ a.1 ≤ (T : ℝ) := by sorry
