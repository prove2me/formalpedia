-- Prove2me | Theorems.Thm_BookProof_IrreversibleDynamics_finite_no_irreversible
-- name    : BookProof.IrreversibleDynamics.finite_no_irreversible
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:19:32.924619+00:00
-- url     : https://prove2.me/theorems/0af77572-0306-4003-ba75-60abecbe276d
-- title:
--   `BookProof.IrreversibleDynamics.finite_no_irreversible` {α : Type*} [Finite α] : ¬ ∃ f : α → α, Function.Injective f ∧ ¬ Function.Surjective f
-- statement:
--   Prove the following Lean 4 theorem from `ChapterIrreversibleDynamics`.
--
--   `BookProof.IrreversibleDynamics.finite_no_irreversible` {α : Type*} [Finite α] : ¬ ∃ f : α → α, Function.Injective f ∧ ¬ Function.Surjective f
--
--   Formalization note: Lean 4 identifier `BookProof.IrreversibleDynamics.finite_no_irreversible`.

-- Generated from ChapterIrreversibleDynamics.lean — theorem BookProof.IrreversibleDynamics.finite_no_irreversible
import Mathlib
import Definitions.Def_ChapterIrreversibleDynamics
open BookProof.IrreversibleDynamics



open MeasureTheory Function Set
open scoped ENNReal

theorem BookProof.IrreversibleDynamics.finite_no_irreversible {α : Type*} [Finite α] :
    ¬ ∃ f : α → α, Function.Injective f ∧ ¬ Function.Surjective f := by sorry
