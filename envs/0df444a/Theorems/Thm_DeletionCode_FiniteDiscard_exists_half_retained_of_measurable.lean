-- Prove2me | Theorems.Thm_DeletionCode_FiniteDiscard_exists_half_retained_of_measurable
-- name    : DeletionCode.FiniteDiscard.exists_half_retained_of_measurable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:48:44.887983+00:00
-- url     : https://prove2.me/theorems/dfba6e22-0be5-41b8-94c9-d0af7e2848fd
-- title:
--   Finite Discard: exists half retained of measurable
-- statement:
--   The averaging step for measurable bad events.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteDiscard.lean#L29-L69
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/FiniteDiscard.lean#L29-L69

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

theorem DeletionCode.FiniteDiscard.exists_half_retained_of_measurable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Finset V) (E : V → Set Ω)
    (hmeas : ∀ v ∈ s, MeasurableSet (E v))
    (hE : ∀ v ∈ s, μ (E v) ≤ ENNReal.ofReal (1 / 3 : ℝ)) :
    ∃ ω, s.card ≤ 2 * (s.filter (fun v => ω ∉ E v)).card := by sorry
