-- Prove2me | Theorems.Thm_BookProof_ChapterLorentzRealRepFull_gram_twoR
-- name    : BookProof.ChapterLorentzRealRepFull.gram_twoR
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:40:16.517277+00:00
-- url     : https://prove2.me/theorems/10df4b97-1e5a-4466-bd95-e32d4c85ca72
-- title:
--   `BookProof.ChapterLorentzRealRepFull.gram_twoR` : ∀ i j : Fin 2, ((w2R i)ᵀ * w2R j).trace = if i = j then (4 : ℝ) else 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzRealRepFull`.
--
--   `BookProof.ChapterLorentzRealRepFull.gram_twoR` : ∀ i j : Fin 2, ((w2R i)ᵀ * w2R j).trace = if i = j then (4 : ℝ) else 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLorentzRealRepFull.gram_twoR`.

-- Generated from ChapterLorentzRealRepFull.lean — theorem BookProof.ChapterLorentzRealRepFull.gram_twoR
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinOmega
import Definitions.Def_ChapterLorentzRealRepSum
import Mathlib
import Definitions.Def_ChapterLorentzRealRepFull
import Definitions.Def_ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRepFull


open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega BookProof.ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRepSum
open Module

theorem BookProof.ChapterLorentzRealRepFull.gram_twoR : ∀ i j : Fin 2, ((w2R i)ᵀ * w2R j).trace = if i = j then (4 : ℝ) else 0 := by sorry
