-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux20_finite_mark_simple_eapprox_supr
-- name    : AvramDividend.Classical.avram_redux20_finite_mark_simple_eapprox_supr
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T08:52:23.915314+00:00
-- url     : https://prove2.me/theorems/c7434351-441c-4169-822a-ae07e5aad404
-- title:
--   Simple-function approximation recovers the exact finite physical marked loss
-- statement:
--   For the actual finite set of negative jump marks selected by any strict cutoff, applying the canonical monotone simple-function approximation to a nonnegative Borel marked loss commutes with summing over those marks. It is a precise limit bridge from finite simple marked counts to the original physical jump loss.
-- source:
--   Use SimpleFunc.monotone_eapprox, the published finite directed-supremum interchange, and SimpleFunc.iSup_eapprox_apply from the pinned Mathlib revision. This statement is generic in the finite mark support so it applies to the source-exact original Levy jump set.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_redux20_finite_mark_simple_eapprox_supr
    {α : Type*} [MeasurableSpace α]
    (S : Finset α) (f : α → ℝ≥0∞) (hf : Measurable f) :
    (⨆ n : ℕ, ∑ a ∈ S, MeasureTheory.SimpleFunc.eapprox f n a) =
      ∑ a ∈ S, f a := by sorry
