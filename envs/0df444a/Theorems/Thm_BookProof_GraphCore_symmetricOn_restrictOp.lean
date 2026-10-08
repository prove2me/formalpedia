-- Prove2me | Theorems.Thm_BookProof_GraphCore_symmetricOn_restrictOp
-- name    : BookProof.GraphCore.symmetricOn_restrictOp
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T12:56:29.921079+00:00
-- url     : https://prove2.me/theorems/5dbaa9bf-f7e9-4775-a1fd-31b8e64cd2d3
-- title:
--   `BookProof.GraphCore.symmetricOn_restrictOp` {D₁ D₂ : Submodule ℂ F} (T : D₂ →ₗ[ℂ] F) (h : D₁ ≤ D₂) (hT : SymmetricOn D₂ T) : SymmetricOn D₁ (restrictOp T h)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGraphCoreTransfer`.
--
--   `BookProof.GraphCore.symmetricOn_restrictOp` {D₁ D₂ : Submodule ℂ F} (T : D₂ →ₗ[ℂ] F) (h : D₁ ≤ D₂) (hT : SymmetricOn D₂ T) : SymmetricOn D₁ (restrictOp T h)
--
--   Formalization note: Lean 4 identifier `BookProof.GraphCore.symmetricOn_restrictOp`.

-- Generated from ChapterGraphCoreTransfer.lean — theorem BookProof.GraphCore.symmetricOn_restrictOp
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterFarisLavineCore
open BookProof.GraphCore



open BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.GraphCore.symmetricOn_restrictOp {D₁ D₂ : Submodule ℂ F} (T : D₂ →ₗ[ℂ] F) (h : D₁ ≤ D₂)
    (hT : SymmetricOn D₂ T) : SymmetricOn D₁ (restrictOp T h) := by sorry
