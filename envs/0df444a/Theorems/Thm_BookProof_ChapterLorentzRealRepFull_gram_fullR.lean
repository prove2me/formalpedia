-- Prove2me | Theorems.Thm_BookProof_ChapterLorentzRealRepFull_gram_fullR
-- name    : BookProof.ChapterLorentzRealRepFull.gram_fullR
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:41:34.054679+00:00
-- url     : https://prove2.me/theorems/af1ab2d8-4649-497d-8d8e-488b8dba389d
-- title:
--   `BookProof.ChapterLorentzRealRepFull.gram_fullR` : ∀ i j : Fin 16, ((bFullR i)ᵀ * bFullR j).trace = if i = j then (4 : ℝ) else 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzRealRepFull`.
--
--   `BookProof.ChapterLorentzRealRepFull.gram_fullR` : ∀ i j : Fin 16, ((bFullR i)ᵀ * bFullR j).trace = if i = j then (4 : ℝ) else 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLorentzRealRepFull.gram_fullR`.

-- Generated from ChapterLorentzRealRepFull.lean — theorem BookProof.ChapterLorentzRealRepFull.gram_fullR
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

theorem BookProof.ChapterLorentzRealRepFull.gram_fullR :
    ∀ i j : Fin 16, ((bFullR i)ᵀ * bFullR j).trace = if i = j then (4 : ℝ) else 0 := by sorry
