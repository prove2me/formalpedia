-- Prove2me | Theorems.Thm_BookProof_ChapterLorentzRealRepFull_range_bFullR
-- name    : BookProof.ChapterLorentzRealRepFull.range_bFullR
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:42:05.287557+00:00
-- url     : https://prove2.me/theorems/919430f8-3263-4944-b3be-5545d74ced58
-- title:
--   `BookProof.ChapterLorentzRealRepFull.range_bFullR` : Set.range bFullR = ((Set.range bHalfR ∪ Set.range b10R) ∪ Set.range bPsR) ∪ Set.range w2R
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzRealRepFull`.
--
--   `BookProof.ChapterLorentzRealRepFull.range_bFullR` : Set.range bFullR = ((Set.range bHalfR ∪ Set.range b10R) ∪ Set.range bPsR) ∪ Set.range w2R
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLorentzRealRepFull.range_bFullR`.

-- Generated from ChapterLorentzRealRepFull.lean — theorem BookProof.ChapterLorentzRealRepFull.range_bFullR
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

theorem BookProof.ChapterLorentzRealRepFull.range_bFullR :
    Set.range bFullR
      = ((Set.range bHalfR ∪ Set.range b10R) ∪ Set.range bPsR) ∪ Set.range w2R := by sorry
