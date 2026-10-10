-- Prove2me | Theorems.Thm_BookProof_ChapterLorentzRealRepSum_gram_all
-- name    : BookProof.ChapterLorentzRealRepSum.gram_all
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:43:47.176353+00:00
-- url     : https://prove2.me/theorems/7c01be1b-accc-48e2-ae29-742042d1207c
-- title:
--   `BookProof.ChapterLorentzRealRepSum.gram_all` : ∀ i j : Fin 14, ((bAll i)ᵀ * bAll j).trace = if i = j then 4 else 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzRealRepSum`.
--
--   `BookProof.ChapterLorentzRealRepSum.gram_all` : ∀ i j : Fin 14, ((bAll i)ᵀ * bAll j).trace = if i = j then 4 else 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLorentzRealRepSum.gram_all`.

-- Generated from ChapterLorentzRealRepSum.lean — theorem BookProof.ChapterLorentzRealRepSum.gram_all
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinOmega
import Definitions.Def_ChapterLorentzRealRep
import Mathlib
import Definitions.Def_ChapterLorentzRealRepSum
open BookProof.ChapterLorentzRealRepSum


open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega BookProof.ChapterLorentzRealRep
open Module

theorem BookProof.ChapterLorentzRealRepSum.gram_all : ∀ i j : Fin 14, ((bAll i)ᵀ * bAll j).trace = if i = j then 4 else 0 := by sorry
