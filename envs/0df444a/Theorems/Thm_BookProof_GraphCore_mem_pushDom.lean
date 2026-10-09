-- Prove2me | Theorems.Thm_BookProof_GraphCore_mem_pushDom
-- name    : BookProof.GraphCore.mem_pushDom
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T12:57:04.606414+00:00
-- url     : https://prove2.me/theorems/e7e22e61-b55d-4bc7-acf0-af35517cc0fd
-- title:
--   `BookProof.GraphCore.mem_pushDom` (U : F →ₗᵢ[ℂ] G) {D : Submodule ℂ F} (x : D) : U (x : F) ∈ pushDom U D
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGraphCoreTransfer`.
--
--   `BookProof.GraphCore.mem_pushDom` (U : F →ₗᵢ[ℂ] G) {D : Submodule ℂ F} (x : D) : U (x : F) ∈ pushDom U D
--
--   Formalization note: Lean 4 identifier `BookProof.GraphCore.mem_pushDom`.

-- Generated from ChapterGraphCoreTransfer.lean — theorem BookProof.GraphCore.mem_pushDom
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterGraphCoreTransfer
open BookProof.GraphCore



open BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]

theorem BookProof.GraphCore.mem_pushDom (U : F →ₗᵢ[ℂ] G) {D : Submodule ℂ F} (x : D) :
    U (x : F) ∈ pushDom U D := by sorry
