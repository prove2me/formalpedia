-- Prove2me | Theorems.Thm_BookProof_ChapterLorentzRealRep_gram_ps
-- name    : BookProof.ChapterLorentzRealRep.gram_ps
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:24:10.127976+00:00
-- url     : https://prove2.me/theorems/fc999233-567a-4dcf-987b-e0b3d2d9d965
-- title:
--   `BookProof.ChapterLorentzRealRep.gram_ps` : ∀ i j : Fin 4, ((bPs i)ᵀ * bPs j).trace = if i = j then 4 else 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzRealRep`.
--
--   `BookProof.ChapterLorentzRealRep.gram_ps` : ∀ i j : Fin 4, ((bPs i)ᵀ * bPs j).trace = if i = j then 4 else 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLorentzRealRep.gram_ps`.

-- Generated from ChapterLorentzRealRep.lean — theorem BookProof.ChapterLorentzRealRep.gram_ps
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinOmega
import Mathlib
import Definitions.Def_ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRep


open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega

theorem BookProof.ChapterLorentzRealRep.gram_ps : ∀ i j : Fin 4, ((bPs i)ᵀ * bPs j).trace = if i = j then 4 else 0 := by sorry
