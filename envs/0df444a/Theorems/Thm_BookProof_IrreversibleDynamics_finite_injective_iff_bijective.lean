-- Prove2me | Theorems.Thm_BookProof_IrreversibleDynamics_finite_injective_iff_bijective
-- name    : BookProof.IrreversibleDynamics.finite_injective_iff_bijective
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:19:24.380826+00:00
-- url     : https://prove2.me/theorems/c0cc150f-0735-43e2-833b-21fe7c2c0556
-- title:
--   `BookProof.IrreversibleDynamics.finite_injective_iff_bijective` {α : Type*} [Finite α] (f : α → α) : Function.Injective f ↔ Function.Bijective f
-- statement:
--   Prove the following Lean 4 theorem from `ChapterIrreversibleDynamics`.
--
--   `BookProof.IrreversibleDynamics.finite_injective_iff_bijective` {α : Type*} [Finite α] (f : α → α) : Function.Injective f ↔ Function.Bijective f
--
--   Formalization note: Lean 4 identifier `BookProof.IrreversibleDynamics.finite_injective_iff_bijective`.

-- Generated from ChapterIrreversibleDynamics.lean — theorem BookProof.IrreversibleDynamics.finite_injective_iff_bijective
import Mathlib
import Definitions.Def_ChapterIrreversibleDynamics
open BookProof.IrreversibleDynamics



open MeasureTheory Function Set
open scoped ENNReal

theorem BookProof.IrreversibleDynamics.finite_injective_iff_bijective {α : Type*} [Finite α] (f : α → α) :
    Function.Injective f ↔ Function.Bijective f := by sorry
