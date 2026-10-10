-- Prove2me | Theorems.Thm_BookProof_ChapterLorentzRealRepFull_gram_two
-- name    : BookProof.ChapterLorentzRealRepFull.gram_two
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:39:46.204398+00:00
-- url     : https://prove2.me/theorems/9f44fe52-941f-47e4-860a-7990d859752f
-- title:
--   `BookProof.ChapterLorentzRealRepFull.gram_two` : ∀ i j : Fin 2, ((w2 i)ᵀ * w2 j).trace = if i = j then 4 else 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzRealRepFull`.
--
--   `BookProof.ChapterLorentzRealRepFull.gram_two` : ∀ i j : Fin 2, ((w2 i)ᵀ * w2 j).trace = if i = j then 4 else 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLorentzRealRepFull.gram_two`.

-- Generated from ChapterLorentzRealRepFull.lean — theorem BookProof.ChapterLorentzRealRepFull.gram_two
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinOmega
import Definitions.Def_ChapterLorentzRealRep
import Definitions.Def_ChapterLorentzRealRepSum
import Mathlib
import Definitions.Def_ChapterLorentzRealRepFull
open BookProof.ChapterLorentzRealRepFull


open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega BookProof.ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRepSum
open Module

theorem BookProof.ChapterLorentzRealRepFull.gram_two : ∀ i j : Fin 2, ((w2 i)ᵀ * w2 j).trace = if i = j then 4 else 0 := by sorry
