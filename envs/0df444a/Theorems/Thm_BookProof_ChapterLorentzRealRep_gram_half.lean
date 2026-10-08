-- Prove2me | Theorems.Thm_BookProof_ChapterLorentzRealRep_gram_half
-- name    : BookProof.ChapterLorentzRealRep.gram_half
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:23:42.875984+00:00
-- url     : https://prove2.me/theorems/70f99249-7043-497e-a8ff-2b11a7818a18
-- title:
--   `BookProof.ChapterLorentzRealRep.gram_half` : ∀ i j : Fin 4, ((bHalf i)ᵀ * bHalf j).trace = if i = j then 4 else 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzRealRep`.
--
--   `BookProof.ChapterLorentzRealRep.gram_half` : ∀ i j : Fin 4, ((bHalf i)ᵀ * bHalf j).trace = if i = j then 4 else 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLorentzRealRep.gram_half`.

-- Generated from ChapterLorentzRealRep.lean — theorem BookProof.ChapterLorentzRealRep.gram_half
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinOmega
import Mathlib
import Definitions.Def_ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRep


open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega

theorem BookProof.ChapterLorentzRealRep.gram_half : ∀ i j : Fin 4, ((bHalf i)ᵀ * bHalf j).trace = if i = j then 4 else 0 := by sorry
