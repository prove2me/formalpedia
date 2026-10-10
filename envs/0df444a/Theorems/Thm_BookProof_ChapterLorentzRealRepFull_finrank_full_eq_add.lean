-- Prove2me | Theorems.Thm_BookProof_ChapterLorentzRealRepFull_finrank_full_eq_add
-- name    : BookProof.ChapterLorentzRealRepFull.finrank_full_eq_add
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:42:50.302691+00:00
-- url     : https://prove2.me/theorems/fc4d4077-fef0-4433-9a6a-456d01bf5150
-- title:
--   `BookProof.ChapterLorentzRealRepFull.finrank_full_eq_add` : finrank ℝ (Matrix (Fin 4) (Fin 4) ℝ) = finrank ℝ WHalf + finrank ℝ W10 + finrank ℝ WPs + finrank ℝ WTwo
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzRealRepFull`.
--
--   `BookProof.ChapterLorentzRealRepFull.finrank_full_eq_add` : finrank ℝ (Matrix (Fin 4) (Fin 4) ℝ) = finrank ℝ WHalf + finrank ℝ W10 + finrank ℝ WPs + finrank ℝ WTwo
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLorentzRealRepFull.finrank_full_eq_add`.

-- Generated from ChapterLorentzRealRepFull.lean — theorem BookProof.ChapterLorentzRealRepFull.finrank_full_eq_add
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

theorem BookProof.ChapterLorentzRealRepFull.finrank_full_eq_add :
    finrank ℝ (Matrix (Fin 4) (Fin 4) ℝ)
      = finrank ℝ WHalf + finrank ℝ W10 + finrank ℝ WPs + finrank ℝ WTwo := by sorry
