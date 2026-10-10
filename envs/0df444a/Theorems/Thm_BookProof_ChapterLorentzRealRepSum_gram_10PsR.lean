-- Prove2me | Theorems.Thm_BookProof_ChapterLorentzRealRepSum_gram_10PsR
-- name    : BookProof.ChapterLorentzRealRepSum.gram_10PsR
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:43:36.834635+00:00
-- url     : https://prove2.me/theorems/9a0cb569-3755-4433-96fa-8fbcb3f160b1
-- title:
--   `BookProof.ChapterLorentzRealRepSum.gram_10PsR` : ∀ (i : Fin 6) (j : Fin 4), ((b10R i)ᵀ * bPsR j).trace = (0 : ℝ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzRealRepSum`.
--
--   `BookProof.ChapterLorentzRealRepSum.gram_10PsR` : ∀ (i : Fin 6) (j : Fin 4), ((b10R i)ᵀ * bPsR j).trace = (0 : ℝ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLorentzRealRepSum.gram_10PsR`.

-- Generated from ChapterLorentzRealRepSum.lean — theorem BookProof.ChapterLorentzRealRepSum.gram_10PsR
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

theorem BookProof.ChapterLorentzRealRepSum.gram_10PsR : ∀ (i : Fin 6) (j : Fin 4), ((b10R i)ᵀ * bPsR j).trace = (0 : ℝ) := by sorry
