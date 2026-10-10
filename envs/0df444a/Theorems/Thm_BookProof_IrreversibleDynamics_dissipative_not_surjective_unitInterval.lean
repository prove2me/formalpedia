-- Prove2me | Theorems.Thm_BookProof_IrreversibleDynamics_dissipative_not_surjective_unitInterval
-- name    : BookProof.IrreversibleDynamics.dissipative_not_surjective_unitInterval
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:20:18.876361+00:00
-- url     : https://prove2.me/theorems/4c4bb4c8-5093-474a-bb3b-429243283e8e
-- title:
--   `BookProof.IrreversibleDynamics.dissipative_not_surjective_unitInterval` : ∃ y ∈ Set.Icc (0 : ℝ) 1, y ∉ dissipative '' Set.Icc (0 : ℝ) 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterIrreversibleDynamics`.
--
--   `BookProof.IrreversibleDynamics.dissipative_not_surjective_unitInterval` : ∃ y ∈ Set.Icc (0 : ℝ) 1, y ∉ dissipative '' Set.Icc (0 : ℝ) 1
--
--   Formalization note: Lean 4 identifier `BookProof.IrreversibleDynamics.dissipative_not_surjective_unitInterval`.

-- Generated from ChapterIrreversibleDynamics.lean — theorem BookProof.IrreversibleDynamics.dissipative_not_surjective_unitInterval
import Mathlib
import Definitions.Def_ChapterIrreversibleDynamics
open BookProof.IrreversibleDynamics



open MeasureTheory Function Set
open scoped ENNReal

theorem BookProof.IrreversibleDynamics.dissipative_not_surjective_unitInterval :
    ∃ y ∈ Set.Icc (0 : ℝ) 1, y ∉ dissipative '' Set.Icc (0 : ℝ) 1 := by sorry
