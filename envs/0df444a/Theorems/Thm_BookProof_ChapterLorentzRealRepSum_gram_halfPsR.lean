-- Prove2me | Theorems.Thm_BookProof_ChapterLorentzRealRepSum_gram_halfPsR
-- name    : BookProof.ChapterLorentzRealRepSum.gram_halfPsR
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:43:32.709059+00:00
-- url     : https://prove2.me/theorems/7c03dbb2-c43d-4ba6-8b66-9c1bd4ecaa4d
-- title:
--   `BookProof.ChapterLorentzRealRepSum.gram_halfPsR` : ∀ (i j : Fin 4), ((bHalfR i)ᵀ * bPsR j).trace = (0 : ℝ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzRealRepSum`.
--
--   `BookProof.ChapterLorentzRealRepSum.gram_halfPsR` : ∀ (i j : Fin 4), ((bHalfR i)ᵀ * bPsR j).trace = (0 : ℝ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLorentzRealRepSum.gram_halfPsR`.

-- Generated from ChapterLorentzRealRepSum.lean — theorem BookProof.ChapterLorentzRealRepSum.gram_halfPsR
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

theorem BookProof.ChapterLorentzRealRepSum.gram_halfPsR : ∀ (i j : Fin 4), ((bHalfR i)ᵀ * bPsR j).trace = (0 : ℝ) := by sorry
