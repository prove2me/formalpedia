-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornSignHom_flipVec_injective
-- name    : BookProof.ChapterFreeFieldBornSignHom.flipVec_injective
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T07:42:55.485536+00:00
-- url     : https://prove2.me/theorems/63932b26-62e0-484d-9241-3eafebcfba98
-- title:
--   `BookProof.ChapterFreeFieldBornSignHom.flipVec_injective` : Function.Injective (flipVec : (Fin n → Bool) → (Fin n → ℝ))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornSignHom`.
--
--   `BookProof.ChapterFreeFieldBornSignHom.flipVec_injective` : Function.Injective (flipVec : (Fin n → Bool) → (Fin n → ℝ))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornSignHom.flipVec_injective`.

-- Generated from ChapterFreeFieldBornSignHom.lean — theorem BookProof.ChapterFreeFieldBornSignHom.flipVec_injective
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

theorem BookProof.ChapterFreeFieldBornSignHom.flipVec_injective : Function.Injective (flipVec : (Fin n → Bool) → (Fin n → ℝ)) := by sorry
