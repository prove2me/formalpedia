-- Prove2me | Theorems.Thm_BookProof_ChapterLorentzRealRep_castR_mul
-- name    : BookProof.ChapterLorentzRealRep.castR_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:24:11.546512+00:00
-- url     : https://prove2.me/theorems/29de8e46-4ef1-43cd-9ab9-5fd673631e06
-- title:
--   `BookProof.ChapterLorentzRealRep.castR_mul` (A B : Matrix (Fin 4) (Fin 4) ℤ) : castR (A * B) = castR A * castR B
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzRealRep`.
--
--   `BookProof.ChapterLorentzRealRep.castR_mul` (A B : Matrix (Fin 4) (Fin 4) ℤ) : castR (A * B) = castR A * castR B
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLorentzRealRep.castR_mul`.

-- Generated from ChapterLorentzRealRep.lean — theorem BookProof.ChapterLorentzRealRep.castR_mul
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinOmega
import Mathlib
import Definitions.Def_ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRep


open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega

theorem BookProof.ChapterLorentzRealRep.castR_mul (A B : Matrix (Fin 4) (Fin 4) ℤ) : castR (A * B) = castR A * castR B := by sorry
