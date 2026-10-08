-- Prove2me | Theorems.Thm_BookProof_ChapterLorentzRealRep_gram_halfR
-- name    : BookProof.ChapterLorentzRealRep.gram_halfR
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:24:38.583978+00:00
-- url     : https://prove2.me/theorems/047f714b-5f39-4af6-baef-7a15ef9044fb
-- title:
--   `BookProof.ChapterLorentzRealRep.gram_halfR` : ∀ i j : Fin 4, ((bHalfR i)ᵀ * bHalfR j).trace = if i = j then (4 : ℝ) else 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzRealRep`.
--
--   `BookProof.ChapterLorentzRealRep.gram_halfR` : ∀ i j : Fin 4, ((bHalfR i)ᵀ * bHalfR j).trace = if i = j then (4 : ℝ) else 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLorentzRealRep.gram_halfR`.

-- Generated from ChapterLorentzRealRep.lean — theorem BookProof.ChapterLorentzRealRep.gram_halfR
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinOmega
import Mathlib
import Definitions.Def_ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRep


open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega

theorem BookProof.ChapterLorentzRealRep.gram_halfR :
    ∀ i j : Fin 4, ((bHalfR i)ᵀ * bHalfR j).trace = if i = j then (4 : ℝ) else 0 := by sorry
