-- Prove2me | Theorems.Thm_BookProof_IrreversibleDynamics_finite_injective_iff_surjective
-- name    : BookProof.IrreversibleDynamics.finite_injective_iff_surjective
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:19:22.223619+00:00
-- url     : https://prove2.me/theorems/670fdfae-416f-4a89-8b6c-ec34c0c33f4b
-- title:
--   `BookProof.IrreversibleDynamics.finite_injective_iff_surjective` {α : Type*} [Finite α] (f : α → α) : Function.Injective f ↔ Function.Surjective f
-- statement:
--   Prove the following Lean 4 theorem from `ChapterIrreversibleDynamics`.
--
--   `BookProof.IrreversibleDynamics.finite_injective_iff_surjective` {α : Type*} [Finite α] (f : α → α) : Function.Injective f ↔ Function.Surjective f
--
--   Formalization note: Lean 4 identifier `BookProof.IrreversibleDynamics.finite_injective_iff_surjective`.

-- Generated from ChapterIrreversibleDynamics.lean — theorem BookProof.IrreversibleDynamics.finite_injective_iff_surjective
import Mathlib
import Definitions.Def_ChapterIrreversibleDynamics
open BookProof.IrreversibleDynamics



open MeasureTheory Function Set
open scoped ENNReal

theorem BookProof.IrreversibleDynamics.finite_injective_iff_surjective {α : Type*} [Finite α] (f : α → α) :
    Function.Injective f ↔ Function.Surjective f := by sorry
