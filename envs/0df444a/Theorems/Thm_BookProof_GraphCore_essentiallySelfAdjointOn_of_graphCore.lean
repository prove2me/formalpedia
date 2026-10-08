-- Prove2me | Theorems.Thm_BookProof_GraphCore_essentiallySelfAdjointOn_of_graphCore
-- name    : BookProof.GraphCore.essentiallySelfAdjointOn_of_graphCore
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T12:56:29.216094+00:00
-- url     : https://prove2.me/theorems/0b3e6a8c-fb91-4cc7-b4ea-b236f91a3fa2
-- title:
--   `BookProof.GraphCore.essentiallySelfAdjointOn_of_graphCore` {D₁ D₂ : Submodule ℂ F} (T : D₂ →ₗ[ℂ] F) (h : D₁ ≤ D₂) (hcore : IsGraphCore D₁ T) (hesa :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGraphCoreTransfer`.
--
--   `BookProof.GraphCore.essentiallySelfAdjointOn_of_graphCore` {D₁ D₂ : Submodule ℂ F} (T : D₂ →ₗ[ℂ] F) (h : D₁ ≤ D₂) (hcore : IsGraphCore D₁ T) (hesa : EssentiallySelfAdjointOn D₂ T) : EssentiallySelfAdjointOn D₁ (restrictOp T h)
--
--   Formalization note: Lean 4 identifier `BookProof.GraphCore.essentiallySelfAdjointOn_of_graphCore`.

-- Generated from ChapterGraphCoreTransfer.lean — theorem BookProof.GraphCore.essentiallySelfAdjointOn_of_graphCore
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterFarisLavineCore
open BookProof.GraphCore



open BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.GraphCore.essentiallySelfAdjointOn_of_graphCore {D₁ D₂ : Submodule ℂ F} (T : D₂ →ₗ[ℂ] F)
    (h : D₁ ≤ D₂) (hcore : IsGraphCore D₁ T)
    (hesa : EssentiallySelfAdjointOn D₂ T) :
    EssentiallySelfAdjointOn D₁ (restrictOp T h) := by sorry
