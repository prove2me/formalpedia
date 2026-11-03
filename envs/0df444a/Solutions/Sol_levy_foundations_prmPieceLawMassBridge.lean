-- Prove2me | solution 1 for levy_foundations_prmPieceLawMassBridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:44:49.266772+00:00
-- url     : https://prove2.me/submissions/b4eaff74-df49-4b7c-a63a-636bddfd9a44

import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Definitions.Def_levy_foundations_prmPieceLaw
import Theorems.Thm_levy_foundations_prmPieceLawOfNonzero
import Theorems.Thm_levy_foundations_prmFinite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

theorem solution
    {E : Type*} [MeasurableSpace E] [Nonempty E]
    (m : Measure E) [SigmaFinite m] (k : ℕ)
    {A : Set E} (hA : MeasurableSet A) :
    (m (LevyFoundations.prmPiece m k)).toReal *
      (LevyFoundations.prmPieceLaw m k).real A =
      (m (LevyFoundations.prmPiece m k ∩ A)).toReal := by
  by_cases h : m (LevyFoundations.prmPiece m k) = 0
  · have hzero : m (LevyFoundations.prmPiece m k ∩ A) = 0 :=
      measure_mono_null Set.inter_subset_left h
    rw [h, ENNReal.toReal_zero, zero_mul, hzero, ENNReal.toReal_zero]
  · rw [levy_foundations_prmPieceLawOfNonzero m k h, measureReal_def,
      Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hA,
      ENNReal.toReal_mul, ENNReal.toReal_inv, ← mul_assoc,
      mul_inv_cancel₀
        (ENNReal.toReal_ne_zero.mpr
          ⟨h, (levy_foundations_prmFinite m k).ne⟩),
      one_mul, Set.inter_comm]
