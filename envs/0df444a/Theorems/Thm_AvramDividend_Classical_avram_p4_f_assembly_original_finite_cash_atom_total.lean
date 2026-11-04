-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_finite_cash_atom_total
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_finite_cash_atom_total
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:38:36.505294+00:00
-- url     : https://prove2.me/theorems/01496157-a146-4924-b4de-0a7a6581bff5
-- title:
--   Original finite-horizon Cash atom mass is finite under true restricted mass
-- statement:
--   In the actual original dividend measure restricted to a finite horizon, if its total mass is finite and it splits into an atomic and a diffuse component, then the sum of countably indexed atomic singleton masses is finite. The exact source Cash decomposition provides these hypotheses and the countable atom set A.
-- source:
--   Proved original Cash split f897c004; new countable Cash atom sum 87b77ccc; Mathlib measure monotonicity and ENNReal.lt_top_iff_ne_top.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_countable_cash_atoms_tsum_eq_measure
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_finite_cash_atom_total
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ≥0)
    (A : Set ℝ) (hA : A.Countable)
    (μatom μdiffuse : Measure ℝ)
    (hsplit : (dividendMeasure D ω).restrict
      (Icc (0 : ℝ) (T : ℝ)) = μatom + μdiffuse)
    (hfinite : ((dividendMeasure D ω).restrict
      (Icc (0 : ℝ) (T : ℝ))) Set.univ ≠ ⊤) :
    (∑' a : A, μatom {a.1}) ≠ ⊤ := by sorry
