-- Prove2me | Theorems.Thm_BookProof_ChapterLorentzRealRepFull_gram_two_PsR
-- name    : BookProof.ChapterLorentzRealRepFull.gram_two_PsR
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:40:53.273696+00:00
-- url     : https://prove2.me/theorems/448fda4a-f04d-4e61-8977-9afb2aa7c407
-- title:
--   `BookProof.ChapterLorentzRealRepFull.gram_two_PsR` : ∀ (i : Fin 2) (j : Fin 4), ((w2R i)ᵀ * bPsR j).trace = (0 : ℝ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzRealRepFull`.
--
--   `BookProof.ChapterLorentzRealRepFull.gram_two_PsR` : ∀ (i : Fin 2) (j : Fin 4), ((w2R i)ᵀ * bPsR j).trace = (0 : ℝ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLorentzRealRepFull.gram_two_PsR`.

-- Generated from ChapterLorentzRealRepFull.lean — theorem BookProof.ChapterLorentzRealRepFull.gram_two_PsR
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

theorem BookProof.ChapterLorentzRealRepFull.gram_two_PsR : ∀ (i : Fin 2) (j : Fin 4), ((w2R i)ᵀ * bPsR j).trace = (0 : ℝ) := by sorry
