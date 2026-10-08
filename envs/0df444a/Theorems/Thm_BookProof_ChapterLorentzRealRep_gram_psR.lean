-- Prove2me | Theorems.Thm_BookProof_ChapterLorentzRealRep_gram_psR
-- name    : BookProof.ChapterLorentzRealRep.gram_psR
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:25:11.304984+00:00
-- url     : https://prove2.me/theorems/ce4f11c8-1781-4557-8da9-47fd4c6c8c1b
-- title:
--   `BookProof.ChapterLorentzRealRep.gram_psR` : ∀ i j : Fin 4, ((bPsR i)ᵀ * bPsR j).trace = if i = j then (4 : ℝ) else 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzRealRep`.
--
--   `BookProof.ChapterLorentzRealRep.gram_psR` : ∀ i j : Fin 4, ((bPsR i)ᵀ * bPsR j).trace = if i = j then (4 : ℝ) else 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLorentzRealRep.gram_psR`.

-- Generated from ChapterLorentzRealRep.lean — theorem BookProof.ChapterLorentzRealRep.gram_psR
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinOmega
import Mathlib
import Definitions.Def_ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRep


open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega

theorem BookProof.ChapterLorentzRealRep.gram_psR : ∀ i j : Fin 4, ((bPsR i)ᵀ * bPsR j).trace = if i = j then (4 : ℝ) else 0 := by sorry
