-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_cash_weighted_atom_tsum_finite_of_mass
-- name    : AvramDividend.Classical.avram_p4_f_assembly_cash_weighted_atom_tsum_finite_of_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:17:41.513844+00:00
-- url     : https://prove2.me/theorems/632713d4-e0b6-427b-bb76-f75bb2c6fd68
-- title:
--   Finite Cash atomic mass bounds discounted subtype-indexed atomic tsum
-- statement:
--   For the source Cash atomic subtype A and atomic measure μatom, when the ENNReal discount/payment selector f is at most one at each indexed atom and the unweighted atomic mass sum is finite, the weighted atomic cash sum is also finite. This is the domination needed to apply the accepted ENNReal-to-real tsum conversion.
-- source:
--   Proved original Cash atom decomposition f897c004, pinned Mathlib ENNReal.tsum_le_tsum and ENNReal.lt_top_iff_ne_top.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_cash_weighted_atom_tsum_finite_of_mass
    (A : Set ℝ) (μatom : Measure ℝ) (f : ℝ → ℝ≥0∞)
    (hf : ∀ a : A, f a.1 ≤ 1)
    (hmass : (∑' a : A, μatom {a.1}) ≠ ⊤) :
    (∑' a : A, f a.1 * μatom {a.1}) ≠ ⊤ := by sorry
