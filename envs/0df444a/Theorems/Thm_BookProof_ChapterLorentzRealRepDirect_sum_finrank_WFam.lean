-- Prove2me | Theorems.Thm_BookProof_ChapterLorentzRealRepDirect_sum_finrank_WFam
-- name    : BookProof.ChapterLorentzRealRepDirect.sum_finrank_WFam
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:38:49.297895+00:00
-- url     : https://prove2.me/theorems/04249d47-7b93-4aff-91a8-884845301d67
-- title:
--   `BookProof.ChapterLorentzRealRepDirect.sum_finrank_WFam` : (∑ i, finrank ℝ (WFam i)) = finrank ℝ (Matrix (Fin 4) (Fin 4) ℝ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzRealRepDirect`.
--
--   `BookProof.ChapterLorentzRealRepDirect.sum_finrank_WFam` : (∑ i, finrank ℝ (WFam i)) = finrank ℝ (Matrix (Fin 4) (Fin 4) ℝ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLorentzRealRepDirect.sum_finrank_WFam`.

-- Generated from ChapterLorentzRealRepDirect.lean — theorem BookProof.ChapterLorentzRealRepDirect.sum_finrank_WFam
import Definitions.Def_ChapterLorentzRealRepSum
import Mathlib
import Definitions.Def_ChapterLorentzRealRepDirect
import Definitions.Def_ChapterLorentzRealRep
import Definitions.Def_ChapterLorentzRealRepFull
open BookProof.ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRepFull
open BookProof.ChapterLorentzRealRepDirect


open Matrix Module


open BookProof.ChapterLorentzRealRep BookProof.ChapterLorentzRealRepSum
open BookProof.ChapterLorentzRealRepFull

theorem BookProof.ChapterLorentzRealRepDirect.sum_finrank_WFam :
    (∑ i, finrank ℝ (WFam i)) = finrank ℝ (Matrix (Fin 4) (Fin 4) ℝ) := by sorry
