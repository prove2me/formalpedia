-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cash_atom_tsum_toReal_and_summable
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_cash_atom_tsum_toReal_and_summable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:10:49.301037+00:00
-- url     : https://prove2.me/theorems/ea9d9c53-5c13-4787-a334-b5c9b6394331
-- title:
--   Subtype-indexed original Cash atom ENNReal tsum converts to real summable series
-- statement:
--   The exact form of the source Cash decomposition's subtype-indexed nonnegative atomic sum can be converted to a summable real atomic series when the ENNReal total and each term are finite. This isolates the finiteness obligations needed before combining Cash with the signed right-dividend residual sum.
-- source:
--   Proved source Cash atom-plus-diffuse decomposition f897c004 and pinned Mathlib ENNReal.summable_toReal, ENNReal.tsum_toReal_eq.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_cash_atom_tsum_toReal_and_summable
    (A : Set ℝ) (μatom : Measure ℝ) (f : ℝ → ℝ≥0∞)
    (hfinite : (∑' a : A, f a.1 * μatom {a.1}) ≠ ⊤)
    (hpoint : ∀ a : A, f a.1 * μatom {a.1} ≠ ⊤) :
    Summable (fun a : A => (f a.1 * μatom {a.1}).toReal) ∧
      (∑' a : A, f a.1 * μatom {a.1}).toReal =
        ∑' a : A, (f a.1 * μatom {a.1}).toReal := by sorry
