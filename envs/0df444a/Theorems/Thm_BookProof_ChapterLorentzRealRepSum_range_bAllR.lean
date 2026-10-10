-- Prove2me | Theorems.Thm_BookProof_ChapterLorentzRealRepSum_range_bAllR
-- name    : BookProof.ChapterLorentzRealRepSum.range_bAllR
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:44:39.74998+00:00
-- url     : https://prove2.me/theorems/bb724ffd-7e48-4ba1-a49b-783d4508258a
-- title:
--   `BookProof.ChapterLorentzRealRepSum.range_bAllR` : Set.range bAllR = Set.range bHalfR ∪ Set.range b10R ∪ Set.range bPsR
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzRealRepSum`.
--
--   `BookProof.ChapterLorentzRealRepSum.range_bAllR` : Set.range bAllR = Set.range bHalfR ∪ Set.range b10R ∪ Set.range bPsR
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLorentzRealRepSum.range_bAllR`.

-- Generated from ChapterLorentzRealRepSum.lean — theorem BookProof.ChapterLorentzRealRepSum.range_bAllR
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

theorem BookProof.ChapterLorentzRealRepSum.range_bAllR :
    Set.range bAllR = Set.range bHalfR ∪ Set.range b10R ∪ Set.range bPsR := by sorry
