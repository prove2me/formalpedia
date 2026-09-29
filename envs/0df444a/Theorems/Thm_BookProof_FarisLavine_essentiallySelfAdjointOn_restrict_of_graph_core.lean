-- Prove2me | Theorems.Thm_BookProof_FarisLavine_essentiallySelfAdjointOn_restrict_of_graph_core
-- name    : BookProof.FarisLavine.essentiallySelfAdjointOn_restrict_of_graph_core
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:18:09.658613+00:00
-- url     : https://prove2.me/theorems/73bf9e48-8cc7-4269-b2b4-ed3ffbdd9391
-- title:
--   The Lean 4 theorem `essentiallySelfAdjointOn_restrict_of_graph_core` in the `ChapterFarisLavineCore` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `essentiallySelfAdjointOn_restrict_of_graph_core` in the `ChapterFarisLavineCore` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFarisLavineCore.lean

-- Generated from ChapterFarisLavineCore.lean — theorem BookProof.FarisLavine.essentiallySelfAdjointOn_restrict_of_graph_core
import Mathlib
import Definitions.Def_ChapterFarisLavineCore
open BookProof.FarisLavine












variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

theorem BookProof.FarisLavine.essentiallySelfAdjointOn_restrict_of_graph_core
    {C : Submodule ℂ F} (hCD : C ≤ D) (H : D →ₗ[ℂ] F)
    (hcore : ∀ (x : D) (ε : ℝ), 0 < ε → ∃ y : D, (y : F) ∈ C ∧
      ‖(y : F) - (x : F)‖ < ε ∧ ‖H y - H x‖ < ε)
    (hdef : EssentiallySelfAdjointOn D H) :
    EssentiallySelfAdjointOn C (H.comp (Submodule.inclusion hCD)) := by sorry
