-- Prove2me | Theorems.Thm_BookProof_ChapterLorentzRealRepSum_gram_halfPs
-- name    : BookProof.ChapterLorentzRealRepSum.gram_halfPs
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:43:04.058809+00:00
-- url     : https://prove2.me/theorems/fd0a49a2-b928-4733-9bce-297981644a98
-- title:
--   `BookProof.ChapterLorentzRealRepSum.gram_halfPs` : ∀ (i j : Fin 4), ((bHalf i)ᵀ * bPs j).trace = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzRealRepSum`.
--
--   `BookProof.ChapterLorentzRealRepSum.gram_halfPs` : ∀ (i j : Fin 4), ((bHalf i)ᵀ * bPs j).trace = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLorentzRealRepSum.gram_halfPs`.

-- Generated from ChapterLorentzRealRepSum.lean — theorem BookProof.ChapterLorentzRealRepSum.gram_halfPs
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinOmega
import Mathlib
import Definitions.Def_ChapterLorentzRealRepSum
import Definitions.Def_ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRepSum


open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega BookProof.ChapterLorentzRealRep
open Module

theorem BookProof.ChapterLorentzRealRepSum.gram_halfPs : ∀ (i j : Fin 4), ((bHalf i)ᵀ * bPs j).trace = 0 := by sorry
