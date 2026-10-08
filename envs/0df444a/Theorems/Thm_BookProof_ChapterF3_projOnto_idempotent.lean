-- Prove2me | Theorems.Thm_BookProof_ChapterF3_projOnto_idempotent
-- name    : BookProof.ChapterF3.projOnto_idempotent
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T03:48:16.552987+00:00
-- url     : https://prove2.me/theorems/6c580c2e-0bf7-4e61-9026-2a711c8c5b64
-- title:
--   `BookProof.ChapterF3.projOnto_idempotent` {ψ : E} (hψ : ‖ψ‖ = 1) (s : E) : projOnto ψ (projOnto ψ s) = projOnto ψ s
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF3`.
--
--   `BookProof.ChapterF3.projOnto_idempotent` {ψ : E} (hψ : ‖ψ‖ = 1) (s : E) : projOnto ψ (projOnto ψ s) = projOnto ψ s
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF3.projOnto_idempotent`.

-- Generated from ChapterF3.lean — theorem BookProof.ChapterF3.projOnto_idempotent
import Mathlib
import Definitions.Def_ChapterF3
open BookProof.ChapterF3


open scoped BigOperators
open Polynomial


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.ChapterF3.projOnto_idempotent {ψ : E} (hψ : ‖ψ‖ = 1) (s : E) :
    projOnto ψ (projOnto ψ s) = projOnto ψ s := by sorry
