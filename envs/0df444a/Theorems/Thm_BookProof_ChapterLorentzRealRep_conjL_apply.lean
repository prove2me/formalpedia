-- Prove2me | Theorems.Thm_BookProof_ChapterLorentzRealRep_conjL_apply
-- name    : BookProof.ChapterLorentzRealRep.conjL_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:25:58.003684+00:00
-- url     : https://prove2.me/theorems/c6ed6300-26bc-42c8-9ffd-5dc264205251
-- title:
--   `BookProof.ChapterLorentzRealRep.conjL_apply` (S T A : Matrix (Fin 4) (Fin 4) ℝ) : conjL S T A = S * A * T
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzRealRep`.
--
--   `BookProof.ChapterLorentzRealRep.conjL_apply` (S T A : Matrix (Fin 4) (Fin 4) ℝ) : conjL S T A = S * A * T
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLorentzRealRep.conjL_apply`.

-- Generated from ChapterLorentzRealRep.lean — theorem BookProof.ChapterLorentzRealRep.conjL_apply
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinOmega
import Mathlib
import Definitions.Def_ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRep


open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega

theorem BookProof.ChapterLorentzRealRep.conjL_apply (S T A : Matrix (Fin 4) (Fin 4) ℝ) : conjL S T A = S * A * T := by sorry
