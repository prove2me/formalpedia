-- Prove2me | Theorems.Thm_BookProof_ChapterLorentzRealRep_W10_invariant
-- name    : BookProof.ChapterLorentzRealRep.W10_invariant
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:37:53.262529+00:00
-- url     : https://prove2.me/theorems/dd60279b-ce1c-4a73-b3ef-774249fd8284
-- title:
--   `BookProof.ChapterLorentzRealRep.W10_invariant` (S : Matrix (Fin 4) (Fin 4) ℤ) (hS : S ∈ Omega) : W10.map (conjL (castR S) (castR (cinv S))) ≤ W10
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzRealRep`.
--
--   `BookProof.ChapterLorentzRealRep.W10_invariant` (S : Matrix (Fin 4) (Fin 4) ℤ) (hS : S ∈ Omega) : W10.map (conjL (castR S) (castR (cinv S))) ≤ W10
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLorentzRealRep.W10_invariant`.

-- Generated from ChapterLorentzRealRep.lean — theorem BookProof.ChapterLorentzRealRep.W10_invariant
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinOmega
import Mathlib
import Definitions.Def_ChapterLorentzRealRep
import Definitions.Def_ChapterPinDoubleCover
open BookProof.ChapterLorentzRealRep


open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega

theorem BookProof.ChapterLorentzRealRep.W10_invariant (S : Matrix (Fin 4) (Fin 4) ℤ) (hS : S ∈ Omega) :
    W10.map (conjL (castR S) (castR (cinv S))) ≤ W10 := by sorry
