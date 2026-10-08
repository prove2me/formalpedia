-- Prove2me | Theorems.Thm_BookProof_ChapterLorentzRealRep_castR_trace
-- name    : BookProof.ChapterLorentzRealRep.castR_trace
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:25:12.901784+00:00
-- url     : https://prove2.me/theorems/bec61c86-535f-4186-a3dd-85734564a5be
-- title:
--   `BookProof.ChapterLorentzRealRep.castR_trace` (A : Matrix (Fin 4) (Fin 4) ℤ) : (castR A).trace = ((A.trace : ℤ) : ℝ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzRealRep`.
--
--   `BookProof.ChapterLorentzRealRep.castR_trace` (A : Matrix (Fin 4) (Fin 4) ℤ) : (castR A).trace = ((A.trace : ℤ) : ℝ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLorentzRealRep.castR_trace`.

-- Generated from ChapterLorentzRealRep.lean — theorem BookProof.ChapterLorentzRealRep.castR_trace
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinOmega
import Mathlib
import Definitions.Def_ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRep


open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega

theorem BookProof.ChapterLorentzRealRep.castR_trace (A : Matrix (Fin 4) (Fin 4) ℤ) : (castR A).trace = ((A.trace : ℤ) : ℝ) := by sorry
