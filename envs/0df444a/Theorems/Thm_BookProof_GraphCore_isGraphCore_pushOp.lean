-- Prove2me | Theorems.Thm_BookProof_GraphCore_isGraphCore_pushOp
-- name    : BookProof.GraphCore.isGraphCore_pushOp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T12:57:41.266979+00:00
-- url     : https://prove2.me/theorems/98c1acc5-5fa8-4ac2-abd9-422e22dee24c
-- title:
--   `BookProof.GraphCore.isGraphCore_pushOp` (U : F →ₗᵢ[ℂ] G) {D₁ D₂ : Submodule ℂ F} (T : D₂ →ₗ[ℂ] F) (hcore : IsGraphCore D₁ T) : IsGraphCore (pushDom U D₁) (pushOp U T)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGraphCoreTransfer`.
--
--   `BookProof.GraphCore.isGraphCore_pushOp` (U : F →ₗᵢ[ℂ] G) {D₁ D₂ : Submodule ℂ F} (T : D₂ →ₗ[ℂ] F) (hcore : IsGraphCore D₁ T) : IsGraphCore (pushDom U D₁) (pushOp U T)
--
--   Formalization note: Lean 4 identifier `BookProof.GraphCore.isGraphCore_pushOp`.

-- Generated from ChapterGraphCoreTransfer.lean — theorem BookProof.GraphCore.isGraphCore_pushOp
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterGraphCoreTransfer
open BookProof.GraphCore



open BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]

theorem BookProof.GraphCore.isGraphCore_pushOp (U : F →ₗᵢ[ℂ] G) {D₁ D₂ : Submodule ℂ F} (T : D₂ →ₗ[ℂ] F)
    (hcore : IsGraphCore D₁ T) : IsGraphCore (pushDom U D₁) (pushOp U T) := by sorry
