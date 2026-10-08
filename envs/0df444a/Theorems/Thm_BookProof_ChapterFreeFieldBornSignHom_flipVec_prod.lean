-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornSignHom_flipVec_prod
-- name    : BookProof.ChapterFreeFieldBornSignHom.flipVec_prod
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T07:55:39.959436+00:00
-- url     : https://prove2.me/theorems/2ee0c6f2-0b0b-40ba-a808-bc60491125bd
-- title:
--   `BookProof.ChapterFreeFieldBornSignHom.flipVec_prod` (b : Fin n → Bool) : (∏ k, flipVec b k) = (-1 : ℝ) ^ flipCount b
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornSignHom`.
--
--   `BookProof.ChapterFreeFieldBornSignHom.flipVec_prod` (b : Fin n → Bool) : (∏ k, flipVec b k) = (-1 : ℝ) ^ flipCount b
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornSignHom.flipVec_prod`.

-- Generated from ChapterFreeFieldBornSignHom.lean — theorem BookProof.ChapterFreeFieldBornSignHom.flipVec_prod
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

theorem BookProof.ChapterFreeFieldBornSignHom.flipVec_prod (b : Fin n → Bool) :
    (∏ k, flipVec b k) = (-1 : ℝ) ^ flipCount b := by sorry
