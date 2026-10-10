-- Prove2me | Theorems.Thm_BookProof_ChapterLorentzRealRep_WHalf_invariant
-- name    : BookProof.ChapterLorentzRealRep.WHalf_invariant
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:37:52.542524+00:00
-- url     : https://prove2.me/theorems/ef22eafa-ec90-48f8-bd12-4809b17b659d
-- title:
--   `BookProof.ChapterLorentzRealRep.WHalf_invariant` (S : Matrix (Fin 4) (Fin 4) ℤ) (hS : S ∈ Omega) : WHalf.map (conjL (castR S) (castR (cinv S))) ≤ WHalf
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzRealRep`.
--
--   `BookProof.ChapterLorentzRealRep.WHalf_invariant` (S : Matrix (Fin 4) (Fin 4) ℤ) (hS : S ∈ Omega) : WHalf.map (conjL (castR S) (castR (cinv S))) ≤ WHalf
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLorentzRealRep.WHalf_invariant`.

-- Generated from ChapterLorentzRealRep.lean — theorem BookProof.ChapterLorentzRealRep.WHalf_invariant
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinOmega
import Mathlib
import Definitions.Def_ChapterLorentzRealRep
import Definitions.Def_ChapterPinDoubleCover
open BookProof.ChapterLorentzRealRep


open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega

theorem BookProof.ChapterLorentzRealRep.WHalf_invariant (S : Matrix (Fin 4) (Fin 4) ℤ) (hS : S ∈ Omega) :
    WHalf.map (conjL (castR S) (castR (cinv S))) ≤ WHalf := by sorry
