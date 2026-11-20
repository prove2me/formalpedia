-- Prove2me | Theorems.Thm_DeletionCode_FiniteDiscard_exists_half_retained
-- name    : DeletionCode.FiniteDiscard.exists_half_retained
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:50:14.58679+00:00
-- url     : https://prove2.me/theorems/c8cff464-257c-4735-bd29-0e509abb3bdb
-- title:
--   Finite Discard: exists half retained
-- statement:
--   No measurability hypothesis is imposed on the bad events. A probability
--   space supplies an outcome even when the finite vertex set is empty.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteDiscard.lean#L74-L87
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteDiscard.lean#L74-L87

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Finiteness
import Definitions.Def_DeletionCode_FiniteDiscard
set_option autoImplicit true
open DeletionCode DeletionCode.FiniteDiscard
open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
variable {Ω V : Type*} [MeasurableSpace Ω] [DecidableEq V]
omit [DecidableEq V]

theorem DeletionCode.FiniteDiscard.exists_half_retained (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Finset V) (E : V → Set Ω)
    (hE : ∀ v ∈ s, μ (E v) ≤ ENNReal.ofReal (1 / 3 : ℝ)) :
    ∃ ω, s.card ≤ 2 * (s.filter (fun v => ω ∉ E v)).card := by sorry
