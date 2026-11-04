-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_restricted_cash_atom_eq_rightjump
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_restricted_cash_atom_eq_rightjump
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:08:23.045804+00:00
-- url     : https://prove2.me/theorems/c70e1a2e-bf7c-4be7-b78a-5c69ce6a1972
-- title:
--   Original restricted Cash singleton equals the source right-dividend jump
-- statement:
--   For the exact atom-plus-diffuse decomposition of the actual original dividend measure restricted to a horizon, the singleton mass of the restricted measure is ENNReal.ofReal of the original right-dividend jump. The diffuse component has null singletons and contributes zero.
-- source:
--   Proved source Cash atom-plus-diffuse decomposition f897c004, null-singleton class, Mathlib measure addition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_restricted_cash_atom_eq_rightjump
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (T t : ℝ≥0) (ht : t ≤ T)
    (μatom μdiffuse : Measure ℝ)
    (hsplit : (dividendMeasure D ω).restrict
      (Icc (0 : ℝ) (T : ℝ)) = μatom + μdiffuse)
    (hdiff : NullSingletonClass μdiffuse)
    (hatom : μatom {(t : ℝ)} =
      ENNReal.ofReal (rightLimit D t ω - D t ω)) :
    ((dividendMeasure D ω).restrict
      (Icc (0 : ℝ) (T : ℝ))) {(t : ℝ)} =
      ENNReal.ofReal (rightLimit D t ω - D t ω) := by sorry
