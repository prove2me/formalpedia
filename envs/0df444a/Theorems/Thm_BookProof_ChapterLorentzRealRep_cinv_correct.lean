-- Prove2me | Theorems.Thm_BookProof_ChapterLorentzRealRep_cinv_correct
-- name    : BookProof.ChapterLorentzRealRep.cinv_correct
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:21:59.835983+00:00
-- url     : https://prove2.me/theorems/9343eff5-5e3f-4c06-8987-ddb6fc31fcda
-- title:
--   `BookProof.ChapterLorentzRealRep.cinv_correct` : ∀ S ∈ Omega, S * cinv S = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzRealRep`.
--
--   `BookProof.ChapterLorentzRealRep.cinv_correct` : ∀ S ∈ Omega, S * cinv S = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLorentzRealRep.cinv_correct`.

-- Generated from ChapterLorentzRealRep.lean — theorem BookProof.ChapterLorentzRealRep.cinv_correct
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinOmega
import Mathlib
import Definitions.Def_ChapterLorentzRealRep
import Definitions.Def_ChapterPinDoubleCover
open BookProof.ChapterLorentzRealRep


open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega

theorem BookProof.ChapterLorentzRealRep.cinv_correct : ∀ S ∈ Omega, S * cinv S = 1 := by sorry
