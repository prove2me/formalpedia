-- Prove2me | Theorems.Thm_BookProof_ChapterF3_projOnto_isSymmetric
-- name    : BookProof.ChapterF3.projOnto_isSymmetric
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-05T13:09:59.75628+00:00
-- url     : https://prove2.me/theorems/1ef69952-62b8-4b3a-82a4-8a3b5bce4fef
-- title:
--   `BookProof.ChapterF3.projOnto_isSymmetric` (ψ : E) (x y : E) : inner (𝕜
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF3`.
--
--   `BookProof.ChapterF3.projOnto_isSymmetric` (ψ : E) (x y : E) : inner (𝕜
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF3.projOnto_isSymmetric`.

-- Generated from ChapterF3.lean — theorem BookProof.ChapterF3.projOnto_isSymmetric
import Mathlib
import Definitions.Def_ChapterF3
open BookProof.ChapterF3


open scoped BigOperators
open Polynomial


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.ChapterF3.projOnto_isSymmetric (ψ : E) (x y : E) :
    inner (𝕜 := ℂ) (projOnto ψ x) y = inner (𝕜 := ℂ) x (projOnto ψ y) := by sorry
