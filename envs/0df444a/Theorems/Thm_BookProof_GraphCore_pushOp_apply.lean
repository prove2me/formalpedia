-- Prove2me | Theorems.Thm_BookProof_GraphCore_pushOp_apply
-- name    : BookProof.GraphCore.pushOp_apply
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T12:57:13.342596+00:00
-- url     : https://prove2.me/theorems/a5de89a7-90de-4e3f-885f-985bef85c2b9
-- title:
--   `BookProof.GraphCore.pushOp_apply` (U : F →ₗᵢ[ℂ] G) {D : Submodule ℂ F} (T : D →ₗ[ℂ] F) (x : pushDom U D) (x₀ : D) (hx : (x : G) = U (x₀ : F)) : pushOp U T x = U (T x₀)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGraphCoreTransfer`.
--
--   `BookProof.GraphCore.pushOp_apply` (U : F →ₗᵢ[ℂ] G) {D : Submodule ℂ F} (T : D →ₗ[ℂ] F) (x : pushDom U D) (x₀ : D) (hx : (x : G) = U (x₀ : F)) : pushOp U T x = U (T x₀)
--
--   Formalization note: Lean 4 identifier `BookProof.GraphCore.pushOp_apply`.

-- Generated from ChapterGraphCoreTransfer.lean — theorem BookProof.GraphCore.pushOp_apply
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterGraphCoreTransfer
open BookProof.GraphCore



open BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]

theorem BookProof.GraphCore.pushOp_apply (U : F →ₗᵢ[ℂ] G) {D : Submodule ℂ F} (T : D →ₗ[ℂ] F)
    (x : pushDom U D) (x₀ : D) (hx : (x : G) = U (x₀ : F)) :
    pushOp U T x = U (T x₀) := by sorry
