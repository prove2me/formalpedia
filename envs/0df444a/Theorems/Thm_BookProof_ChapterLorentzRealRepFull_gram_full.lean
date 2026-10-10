-- Prove2me | Theorems.Thm_BookProof_ChapterLorentzRealRepFull_gram_full
-- name    : BookProof.ChapterLorentzRealRepFull.gram_full
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:41:28.96216+00:00
-- url     : https://prove2.me/theorems/026e744c-ed6e-4e34-80fa-1430ca586325
-- title:
--   `BookProof.ChapterLorentzRealRepFull.gram_full` : ∀ i j : Fin 16, ((bFull i)ᵀ * bFull j).trace = if i = j then 4 else 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzRealRepFull`.
--
--   `BookProof.ChapterLorentzRealRepFull.gram_full` : ∀ i j : Fin 16, ((bFull i)ᵀ * bFull j).trace = if i = j then 4 else 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLorentzRealRepFull.gram_full`.

-- Generated from ChapterLorentzRealRepFull.lean — theorem BookProof.ChapterLorentzRealRepFull.gram_full
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinOmega
import Definitions.Def_ChapterLorentzRealRep
import Definitions.Def_ChapterLorentzRealRepSum
import Mathlib
import Definitions.Def_ChapterLorentzRealRepFull
open BookProof.ChapterLorentzRealRepFull


open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega BookProof.ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRepSum
open Module

theorem BookProof.ChapterLorentzRealRepFull.gram_full : ∀ i j : Fin 16, ((bFull i)ᵀ * bFull j).trace = if i = j then 4 else 0 := by sorry
