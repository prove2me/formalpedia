-- Prove2me | Theorems.Thm_BookProof_IrreversibleDynamics_exists_injective_not_surjective
-- name    : BookProof.IrreversibleDynamics.exists_injective_not_surjective
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:20:57.977594+00:00
-- url     : https://prove2.me/theorems/0f62caed-f0c1-40bb-9f0b-257db6b75806
-- title:
--   `BookProof.IrreversibleDynamics.exists_injective_not_surjective` {α : Type*} [Infinite α] : ∃ f : α → α, Function.Injective f ∧ ¬ Function.Surjective f
-- statement:
--   Prove the following Lean 4 theorem from `ChapterIrreversibleDynamics`.
--
--   `BookProof.IrreversibleDynamics.exists_injective_not_surjective` {α : Type*} [Infinite α] : ∃ f : α → α, Function.Injective f ∧ ¬ Function.Surjective f
--
--   Formalization note: Lean 4 identifier `BookProof.IrreversibleDynamics.exists_injective_not_surjective`.

-- Generated from ChapterIrreversibleDynamics.lean — theorem BookProof.IrreversibleDynamics.exists_injective_not_surjective
import Mathlib
import Definitions.Def_ChapterIrreversibleDynamics
open BookProof.IrreversibleDynamics



open MeasureTheory Function Set
open scoped ENNReal

theorem BookProof.IrreversibleDynamics.exists_injective_not_surjective {α : Type*} [Infinite α] :
    ∃ f : α → α, Function.Injective f ∧ ¬ Function.Surjective f := by sorry
