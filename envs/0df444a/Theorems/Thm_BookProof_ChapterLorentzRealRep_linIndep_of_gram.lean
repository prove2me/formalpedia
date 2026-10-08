-- Prove2me | Theorems.Thm_BookProof_ChapterLorentzRealRep_linIndep_of_gram
-- name    : BookProof.ChapterLorentzRealRep.linIndep_of_gram
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:25:28.731462+00:00
-- url     : https://prove2.me/theorems/b5b7a6ab-10c0-41a1-8ebb-5ec02329c369
-- title:
--   `BookProof.ChapterLorentzRealRep.linIndep_of_gram` {n : ℕ} (v : Fin n → Matrix (Fin 4) (Fin 4) ℝ) (h : ∀ i j, ((v i)ᵀ * v j).trace = if i = j then (4 : ℝ) else 0) : LinearIndepende
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzRealRep`.
--
--   `BookProof.ChapterLorentzRealRep.linIndep_of_gram` {n : ℕ} (v : Fin n → Matrix (Fin 4) (Fin 4) ℝ) (h : ∀ i j, ((v i)ᵀ * v j).trace = if i = j then (4 : ℝ) else 0) : LinearIndependent ℝ v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLorentzRealRep.linIndep_of_gram`.

-- Generated from ChapterLorentzRealRep.lean — theorem BookProof.ChapterLorentzRealRep.linIndep_of_gram
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinOmega
import Mathlib
import Definitions.Def_ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRep


open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega

theorem BookProof.ChapterLorentzRealRep.linIndep_of_gram {n : ℕ} (v : Fin n → Matrix (Fin 4) (Fin 4) ℝ)
    (h : ∀ i j, ((v i)ᵀ * v j).trace = if i = j then (4 : ℝ) else 0) :
    LinearIndependent ℝ v := by sorry
