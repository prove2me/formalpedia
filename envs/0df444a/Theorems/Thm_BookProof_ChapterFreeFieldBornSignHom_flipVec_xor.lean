-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornSignHom_flipVec_xor
-- name    : BookProof.ChapterFreeFieldBornSignHom.flipVec_xor
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T07:42:06.340079+00:00
-- url     : https://prove2.me/theorems/70c88b99-1a64-41dc-a57f-ee829831986e
-- title:
--   `BookProof.ChapterFreeFieldBornSignHom.flipVec_xor` (b₁ b₂ : Fin n → Bool) : flipVec (fun k => xor (b₁ k) (b₂ k)) = flipVec b₁ * flipVec b₂
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornSignHom`.
--
--   `BookProof.ChapterFreeFieldBornSignHom.flipVec_xor` (b₁ b₂ : Fin n → Bool) : flipVec (fun k => xor (b₁ k) (b₂ k)) = flipVec b₁ * flipVec b₂
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornSignHom.flipVec_xor`.

-- Generated from ChapterFreeFieldBornSignHom.lean — theorem BookProof.ChapterFreeFieldBornSignHom.flipVec_xor
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSignGauge
import Definitions.Def_ChapterFreeFieldBornSignAction
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignHom
open BookProof.ChapterFreeFieldBornSignHom

variable {n : ℕ}


open MeasureTheory
open BookProof.ChapterFreeFieldBorn
open BookProof.ChapterFreeFieldBornSignGauge
open BookProof.ChapterFreeFieldBornSignAction

theorem BookProof.ChapterFreeFieldBornSignHom.flipVec_xor (b₁ b₂ : Fin n → Bool) :
    flipVec (fun k => xor (b₁ k) (b₂ k)) = flipVec b₁ * flipVec b₂ := by sorry
