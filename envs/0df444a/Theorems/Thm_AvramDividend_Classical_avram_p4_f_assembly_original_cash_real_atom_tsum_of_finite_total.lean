-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cash_real_atom_tsum_of_finite_total
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_cash_real_atom_tsum_of_finite_total
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:27:58.820684+00:00
-- url     : https://prove2.me/theorems/06ecfaee-b7fd-4cc9-abfc-67511794b5e9
-- title:
--   Finite original Cash atomic ENNReal total alone yields real summability and exact tsum
-- statement:
--   The source Cash decomposition's finite weighted atomic ENNReal total automatically forces every atomic term finite, then the subtype-indexed real atomic terms are summable and the real tsum equals toReal of the ENNReal tsum. Removes the auxiliary individual-atom finiteness assumption from the earlier conversion helper.
-- source:
--   Accepted P4-F exact atomic sum conversion ea9d9c53; pinned Mathlib ENNReal.le_tsum and ENNReal.lt_top_iff_ne_top.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cash_atom_tsum_toReal_and_summable
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_cash_real_atom_tsum_of_finite_total
    (A : Set ℝ) (μatom : Measure ℝ) (f : ℝ → ℝ≥0∞)
    (hfinite : (∑' a : A, f a.1 * μatom {a.1}) ≠ ⊤) :
    Summable (fun a : A => (f a.1 * μatom {a.1}).toReal) ∧
      (∑' a : A, f a.1 * μatom {a.1}).toReal =
        ∑' a : A, (f a.1 * μatom {a.1}).toReal := by sorry
