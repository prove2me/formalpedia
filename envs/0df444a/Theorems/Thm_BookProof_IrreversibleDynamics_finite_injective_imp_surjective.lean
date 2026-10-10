-- Prove2me | Theorems.Thm_BookProof_IrreversibleDynamics_finite_injective_imp_surjective
-- name    : BookProof.IrreversibleDynamics.finite_injective_imp_surjective
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:19:29.763988+00:00
-- url     : https://prove2.me/theorems/6008890c-54dd-42c7-b85a-761831327d32
-- title:
--   `BookProof.IrreversibleDynamics.finite_injective_imp_surjective` {α : Type*} [Finite α] {f : α → α} (hf : Function.Injective f) : Function.Surjective f
-- statement:
--   Prove the following Lean 4 theorem from `ChapterIrreversibleDynamics`.
--
--   `BookProof.IrreversibleDynamics.finite_injective_imp_surjective` {α : Type*} [Finite α] {f : α → α} (hf : Function.Injective f) : Function.Surjective f
--
--   Formalization note: Lean 4 identifier `BookProof.IrreversibleDynamics.finite_injective_imp_surjective`.

-- Generated from ChapterIrreversibleDynamics.lean — theorem BookProof.IrreversibleDynamics.finite_injective_imp_surjective
import Mathlib
import Definitions.Def_ChapterIrreversibleDynamics
open BookProof.IrreversibleDynamics



open MeasureTheory Function Set
open scoped ENNReal

theorem BookProof.IrreversibleDynamics.finite_injective_imp_surjective {α : Type*} [Finite α] {f : α → α}
    (hf : Function.Injective f) : Function.Surjective f := by sorry
