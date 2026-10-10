-- Prove2me | Theorems.Thm_BookProof_ChapterLorentzRealRepSum_gram_allR
-- name    : BookProof.ChapterLorentzRealRepSum.gram_allR
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:43:57.99391+00:00
-- url     : https://prove2.me/theorems/c2782cdd-e63e-4cfc-814a-cec9be621fc8
-- title:
--   `BookProof.ChapterLorentzRealRepSum.gram_allR` : ∀ i j : Fin 14, ((bAllR i)ᵀ * bAllR j).trace = if i = j then (4 : ℝ) else 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzRealRepSum`.
--
--   `BookProof.ChapterLorentzRealRepSum.gram_allR` : ∀ i j : Fin 14, ((bAllR i)ᵀ * bAllR j).trace = if i = j then (4 : ℝ) else 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLorentzRealRepSum.gram_allR`.

-- Generated from ChapterLorentzRealRepSum.lean — theorem BookProof.ChapterLorentzRealRepSum.gram_allR
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

theorem BookProof.ChapterLorentzRealRepSum.gram_allR :
    ∀ i j : Fin 14, ((bAllR i)ᵀ * bAllR j).trace = if i = j then (4 : ℝ) else 0 := by sorry
