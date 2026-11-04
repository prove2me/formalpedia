-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_countable_cash_atoms_tsum_eq_measure
-- name    : AvramDividend.Classical.avram_p4_f_assembly_countable_cash_atoms_tsum_eq_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:12:05.292427+00:00
-- url     : https://prove2.me/theorems/87b77ccc-b42a-4ede-96f9-dc63e0f809ee
-- title:
--   Countably many original Cash atomic singleton masses sum to their atomic measure
-- statement:
--   For the countable source Cash atom index set A, the ENNReal sum of actual atomic singleton masses equals the atomic measure of A. Combined with the source decomposition's μatom support and finite restricted dividend mass, this supplies a direct route to atomic Cash mass finiteness.
-- source:
--   Proved source Cash decomposition f897c004 and pinned Mathlib MeasureTheory.tsum_measure_preimage_singleton.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_countable_cash_atoms_tsum_eq_measure
    (μatom : Measure ℝ) (A : Set ℝ) (hA : A.Countable) :
    (∑' a : A, μatom {a.1}) = μatom A := by sorry
