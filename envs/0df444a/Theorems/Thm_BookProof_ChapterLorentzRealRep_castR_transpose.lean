-- Prove2me | Theorems.Thm_BookProof_ChapterLorentzRealRep_castR_transpose
-- name    : BookProof.ChapterLorentzRealRep.castR_transpose
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:24:19.623046+00:00
-- url     : https://prove2.me/theorems/e7b4605b-7caf-47b0-adb8-3133b10b2753
-- title:
--   `BookProof.ChapterLorentzRealRep.castR_transpose` (A : Matrix (Fin 4) (Fin 4) ℤ) : castR (Aᵀ) = (castR A)ᵀ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzRealRep`.
--
--   `BookProof.ChapterLorentzRealRep.castR_transpose` (A : Matrix (Fin 4) (Fin 4) ℤ) : castR (Aᵀ) = (castR A)ᵀ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLorentzRealRep.castR_transpose`.

-- Generated from ChapterLorentzRealRep.lean — theorem BookProof.ChapterLorentzRealRep.castR_transpose
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinOmega
import Mathlib
import Definitions.Def_ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRep


open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega

theorem BookProof.ChapterLorentzRealRep.castR_transpose (A : Matrix (Fin 4) (Fin 4) ℤ) : castR (Aᵀ) = (castR A)ᵀ := by sorry
