-- Prove2me | Theorems.Thm_BookProof_GraphCore_pushDom_mono
-- name    : BookProof.GraphCore.pushDom_mono
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:51:47.817077+00:00
-- url     : https://prove2.me/theorems/438e7788-6513-4172-af54-1d0326ff79f6
-- title:
--   `BookProof.GraphCore.pushDom_mono` (U : F →ₗᵢ[ℂ] G) {D₁ D₂ : Submodule ℂ F} (h : D₁ ≤ D₂) : pushDom U D₁ ≤ pushDom U D₂
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGraphCoreTransfer`.
--
--   `BookProof.GraphCore.pushDom_mono` (U : F →ₗᵢ[ℂ] G) {D₁ D₂ : Submodule ℂ F} (h : D₁ ≤ D₂) : pushDom U D₁ ≤ pushDom U D₂
--
--   Formalization note: Lean 4 identifier `BookProof.GraphCore.pushDom_mono`.

-- Generated from ChapterGraphCoreTransfer.lean — theorem BookProof.GraphCore.pushDom_mono
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterGraphCoreTransfer
open BookProof.GraphCore



open BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]

theorem BookProof.GraphCore.pushDom_mono (U : F →ₗᵢ[ℂ] G) {D₁ D₂ : Submodule ℂ F} (h : D₁ ≤ D₂) :
    pushDom U D₁ ≤ pushDom U D₂ := by sorry
