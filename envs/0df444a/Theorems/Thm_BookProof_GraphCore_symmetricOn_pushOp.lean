-- Prove2me | Theorems.Thm_BookProof_GraphCore_symmetricOn_pushOp
-- name    : BookProof.GraphCore.symmetricOn_pushOp
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T12:57:21.803987+00:00
-- url     : https://prove2.me/theorems/46e8a82f-6444-4586-9606-7e1266eaef6f
-- title:
--   `BookProof.GraphCore.symmetricOn_pushOp` (U : F →ₗᵢ[ℂ] G) {D : Submodule ℂ F} (T : D →ₗ[ℂ] F) (hT : SymmetricOn D T) : SymmetricOn (pushDom U D) (pushOp U T)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGraphCoreTransfer`.
--
--   `BookProof.GraphCore.symmetricOn_pushOp` (U : F →ₗᵢ[ℂ] G) {D : Submodule ℂ F} (T : D →ₗ[ℂ] F) (hT : SymmetricOn D T) : SymmetricOn (pushDom U D) (pushOp U T)
--
--   Formalization note: Lean 4 identifier `BookProof.GraphCore.symmetricOn_pushOp`.

-- Generated from ChapterGraphCoreTransfer.lean — theorem BookProof.GraphCore.symmetricOn_pushOp
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterFarisLavineCore
open BookProof.GraphCore



open BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]

theorem BookProof.GraphCore.symmetricOn_pushOp (U : F →ₗᵢ[ℂ] G) {D : Submodule ℂ F} (T : D →ₗ[ℂ] F)
    (hT : SymmetricOn D T) : SymmetricOn (pushDom U D) (pushOp U T) := by sorry
