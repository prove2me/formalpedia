-- Prove2me | Theorems.Thm_BookProof_ChapterLorentzRealRep_WPs_invariant
-- name    : BookProof.ChapterLorentzRealRep.WPs_invariant
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:38:15.641866+00:00
-- url     : https://prove2.me/theorems/23c997da-f560-42c3-8b41-881ba8db35d9
-- title:
--   `BookProof.ChapterLorentzRealRep.WPs_invariant` (S : Matrix (Fin 4) (Fin 4) ℤ) (hS : S ∈ Omega) : WPs.map (conjL (castR S) (castR (cinv S))) ≤ WPs
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzRealRep`.
--
--   `BookProof.ChapterLorentzRealRep.WPs_invariant` (S : Matrix (Fin 4) (Fin 4) ℤ) (hS : S ∈ Omega) : WPs.map (conjL (castR S) (castR (cinv S))) ≤ WPs
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLorentzRealRep.WPs_invariant`.

-- Generated from ChapterLorentzRealRep.lean — theorem BookProof.ChapterLorentzRealRep.WPs_invariant
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinOmega
import Mathlib
import Definitions.Def_ChapterLorentzRealRep
import Definitions.Def_ChapterPinDoubleCover
open BookProof.ChapterLorentzRealRep


open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega

theorem BookProof.ChapterLorentzRealRep.WPs_invariant (S : Matrix (Fin 4) (Fin 4) ℤ) (hS : S ∈ Omega) :
    WPs.map (conjL (castR S) (castR (cinv S))) ≤ WPs := by sorry
