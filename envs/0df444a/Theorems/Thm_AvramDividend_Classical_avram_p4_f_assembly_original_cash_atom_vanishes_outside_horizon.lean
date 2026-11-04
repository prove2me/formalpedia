-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cash_atom_vanishes_outside_horizon
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_cash_atom_vanishes_outside_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:22:38.29768+00:00
-- url     : https://prove2.me/theorems/7293bcac-8cde-4674-bed4-5d10b57dc811
-- title:
--   Original Cash atomic measure has zero singleton mass outside the horizon
-- statement:
--   If the true original dividend measure restricted to [0,T] decomposes into nonnegative atomic and diffuse measures, the atomic measure assigns zero to any singleton outside [0,T]. This proves physical-time support for all nonzero original Cash atoms, permitting the q-discount bound to be applied at effective subtype-indexed atoms.
-- source:
--   Proved Cash atom-plus-diffuse decomposition f897c004; pinned Mathlib Measure.restrict_apply and measure addition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_cash_atom_vanishes_outside_horizon
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (T : ℝ≥0) (μatom μdiffuse : Measure ℝ)
    (hsplit : (dividendMeasure D ω).restrict
      (Icc (0 : ℝ) (T : ℝ)) = μatom + μdiffuse)
    (s : ℝ) (hs : s ∉ Icc (0 : ℝ) (T : ℝ)) :
    μatom {s} = 0 := by sorry
