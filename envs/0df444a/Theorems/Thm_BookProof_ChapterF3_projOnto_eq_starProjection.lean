-- Prove2me | Theorems.Thm_BookProof_ChapterF3_projOnto_eq_starProjection
-- name    : BookProof.ChapterF3.projOnto_eq_starProjection
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T03:48:37.862276+00:00
-- url     : https://prove2.me/theorems/8bee4f61-af92-4294-ae21-71101fd78279
-- title:
--   `BookProof.ChapterF3.projOnto_eq_starProjection` {ψ : E} (hψ : ‖ψ‖ = 1) (s : E) : projOnto ψ s = (Submodule.span ℂ {ψ}).starProjection s
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF3`.
--
--   `BookProof.ChapterF3.projOnto_eq_starProjection` {ψ : E} (hψ : ‖ψ‖ = 1) (s : E) : projOnto ψ s = (Submodule.span ℂ {ψ}).starProjection s
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF3.projOnto_eq_starProjection`.

-- Generated from ChapterF3.lean — theorem BookProof.ChapterF3.projOnto_eq_starProjection
import Mathlib
import Definitions.Def_ChapterF3
open BookProof.ChapterF3


open scoped BigOperators
open Polynomial


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.ChapterF3.projOnto_eq_starProjection {ψ : E} (hψ : ‖ψ‖ = 1) (s : E) :
    projOnto ψ s = (Submodule.span ℂ {ψ}).starProjection s := by sorry
