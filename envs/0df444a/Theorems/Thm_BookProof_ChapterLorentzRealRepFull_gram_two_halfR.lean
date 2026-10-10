-- Prove2me | Theorems.Thm_BookProof_ChapterLorentzRealRepFull_gram_two_halfR
-- name    : BookProof.ChapterLorentzRealRepFull.gram_two_halfR
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:40:24.175989+00:00
-- url     : https://prove2.me/theorems/65001826-b6f7-45d7-b065-a340d90de6b0
-- title:
--   `BookProof.ChapterLorentzRealRepFull.gram_two_halfR` : ∀ (i : Fin 2) (j : Fin 4), ((w2R i)ᵀ * bHalfR j).trace = (0 : ℝ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzRealRepFull`.
--
--   `BookProof.ChapterLorentzRealRepFull.gram_two_halfR` : ∀ (i : Fin 2) (j : Fin 4), ((w2R i)ᵀ * bHalfR j).trace = (0 : ℝ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLorentzRealRepFull.gram_two_halfR`.

-- Generated from ChapterLorentzRealRepFull.lean — theorem BookProof.ChapterLorentzRealRepFull.gram_two_halfR
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

theorem BookProof.ChapterLorentzRealRepFull.gram_two_halfR : ∀ (i : Fin 2) (j : Fin 4), ((w2R i)ᵀ * bHalfR j).trace = (0 : ℝ) := by sorry
