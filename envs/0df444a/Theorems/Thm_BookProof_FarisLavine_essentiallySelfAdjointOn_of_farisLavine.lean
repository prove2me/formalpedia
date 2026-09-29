-- Prove2me | Theorems.Thm_BookProof_FarisLavine_essentiallySelfAdjointOn_of_farisLavine
-- name    : BookProof.FarisLavine.essentiallySelfAdjointOn_of_farisLavine
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:56:07.560547+00:00
-- url     : https://prove2.me/theorems/ea2db9b5-c833-4ce2-9455-e4ef4d5b0ed7
-- title:
--   The Lean 4 theorem `essentiallySelfAdjointOn_of_farisLavine` in the `ChapterFarisLavineCore` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `essentiallySelfAdjointOn_of_farisLavine` in the `ChapterFarisLavineCore` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFarisLavineCore.lean

-- Generated from ChapterFarisLavineCore.lean — theorem BookProof.FarisLavine.essentiallySelfAdjointOn_of_farisLavine
import Mathlib
import Definitions.Def_ChapterFarisLavineCore
open BookProof.FarisLavine












variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

theorem BookProof.FarisLavine.essentiallySelfAdjointOn_of_farisLavine [CompleteSpace F]
    (H N : D →ₗ[ℂ] F) (c : ℝ)
    (hH : SymmetricOn D H) (hN : SymmetricOn D N)
    (hc : 0 ≤ c)
    (hNpos : ∀ x : D, 0 ≤ quadForm N x)
    (hNsurj : ∀ f : F, ∃ x : D, N x + (x : F) = f)
    (hcomm : ∀ x : D, |commForm H N x| ≤ c * quadForm N x) :
    EssentiallySelfAdjointOn D H := by sorry
