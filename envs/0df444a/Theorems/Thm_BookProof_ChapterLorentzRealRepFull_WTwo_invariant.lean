-- Prove2me | Theorems.Thm_BookProof_ChapterLorentzRealRepFull_WTwo_invariant
-- name    : BookProof.ChapterLorentzRealRepFull.WTwo_invariant
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:42:13.360556+00:00
-- url     : https://prove2.me/theorems/ed7972ee-e6d2-412b-9dc4-b339536fe7db
-- title:
--   `BookProof.ChapterLorentzRealRepFull.WTwo_invariant` (S : Matrix (Fin 4) (Fin 4) ℤ) (hS : S ∈ Omega) : WTwo.map (conjL (castR S) (castR (cinv S))) ≤ WTwo
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzRealRepFull`.
--
--   `BookProof.ChapterLorentzRealRepFull.WTwo_invariant` (S : Matrix (Fin 4) (Fin 4) ℤ) (hS : S ∈ Omega) : WTwo.map (conjL (castR S) (castR (cinv S))) ≤ WTwo
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLorentzRealRepFull.WTwo_invariant`.

-- Generated from ChapterLorentzRealRepFull.lean — theorem BookProof.ChapterLorentzRealRepFull.WTwo_invariant
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinOmega
import Definitions.Def_ChapterLorentzRealRepSum
import Mathlib
import Definitions.Def_ChapterLorentzRealRepFull
import Definitions.Def_ChapterLorentzRealRep
import Definitions.Def_ChapterPinDoubleCover
open BookProof.ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRepFull


open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega BookProof.ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRepSum
open Module

theorem BookProof.ChapterLorentzRealRepFull.WTwo_invariant (S : Matrix (Fin 4) (Fin 4) ℤ) (hS : S ∈ Omega) :
    WTwo.map (conjL (castR S) (castR (cinv S))) ≤ WTwo := by sorry
