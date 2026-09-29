-- Prove2me | Theorems.Thm_BookProof_FarisLavine_essentiallySelfAdjointOn_core_of_farisLavine
-- name    : BookProof.FarisLavine.essentiallySelfAdjointOn_core_of_farisLavine
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:57:09.850695+00:00
-- url     : https://prove2.me/theorems/7db0d12f-5f2b-4eb5-bab2-8b10ee9a7556
-- title:
--   The Lean 4 theorem `essentiallySelfAdjointOn_core_of_farisLavine` in the `ChapterFarisLavineCore` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `essentiallySelfAdjointOn_core_of_farisLavine` in the `ChapterFarisLavineCore` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFarisLavineCore.lean

-- Generated from ChapterFarisLavineCore.lean — theorem BookProof.FarisLavine.essentiallySelfAdjointOn_core_of_farisLavine
import Mathlib
import Definitions.Def_ChapterFarisLavineCore
open BookProof.FarisLavine












variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

theorem BookProof.FarisLavine.essentiallySelfAdjointOn_core_of_farisLavine [CompleteSpace F]
    {C : Submodule ℂ F} (hCD : C ≤ D) (H N : D →ₗ[ℂ] F) (a b c : ℝ)
    (hH : SymmetricOn D H) (hN : SymmetricOn D N)
    (hc : 0 ≤ c)
    (hNpos : ∀ x : D, 0 ≤ quadForm N x)
    (hNsurj : ∀ f : F, ∃ x : D, N x + (x : F) = f)
    (hcomm : ∀ x : D, |commForm H N x| ≤ c * quadForm N x)
    (hrel : ∀ x : D, ‖H x‖ ^ 2 ≤ a * ‖N x‖ ^ 2 + b * ‖(x : F)‖ ^ 2)
    (hNcore : ∀ (x : D) (ε : ℝ), 0 < ε → ∃ y : D, (y : F) ∈ C ∧
      ‖(y : F) - (x : F)‖ < ε ∧ ‖N y - N x‖ < ε) :
    EssentiallySelfAdjointOn C (H.comp (Submodule.inclusion hCD)) := by sorry
