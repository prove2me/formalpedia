-- Prove2me | Theorems.Thm_BookProof_GraphCore_essentiallySelfAdjointOn_of_bounded_dense
-- name    : BookProof.GraphCore.essentiallySelfAdjointOn_of_bounded_dense
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T12:57:02.915318+00:00
-- url     : https://prove2.me/theorems/020db525-0cdc-4775-8642-d3eb30d0661d
-- title:
--   `BookProof.GraphCore.essentiallySelfAdjointOn_of_bounded_dense` {D : Submodule ℂ F} (T : D →ₗ[ℂ] F) (hT : SymmetricOn D T) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x : D, ‖T x‖ ≤ C *...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGraphCoreTransfer`.
--
--   `BookProof.GraphCore.essentiallySelfAdjointOn_of_bounded_dense` {D : Submodule ℂ F} (T : D →ₗ[ℂ] F) (hT : SymmetricOn D T) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x : D, ‖T x‖ ≤ C * ‖(x : F)‖) (hdense : Dense (D : Set F)) : EssentiallySelfAdjointOn D T
--
--   Formalization note: Lean 4 identifier `BookProof.GraphCore.essentiallySelfAdjointOn_of_bounded_dense`.

-- Generated from ChapterGraphCoreTransfer.lean — theorem BookProof.GraphCore.essentiallySelfAdjointOn_of_bounded_dense
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterFarisLavineCore
open BookProof.GraphCore



open BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.GraphCore.essentiallySelfAdjointOn_of_bounded_dense {D : Submodule ℂ F} (T : D →ₗ[ℂ] F)
    (hT : SymmetricOn D T) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x : D, ‖T x‖ ≤ C * ‖(x : F)‖)
    (hdense : Dense (D : Set F)) :
    EssentiallySelfAdjointOn D T := by sorry
