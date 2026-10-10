-- Prove2me | Theorems.Thm_BookProof_ChapterLorentzRealRepDirect_WFam_conj_invariant
-- name    : BookProof.ChapterLorentzRealRepDirect.WFam_conj_invariant
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:40:01.903034+00:00
-- url     : https://prove2.me/theorems/ecacdab6-e445-4ddf-bb65-48fe114260e8
-- title:
--   `BookProof.ChapterLorentzRealRepDirect.WFam_conj_invariant` (S : Matrix (Fin 4) (Fin 4) ℤ) (hS : S ∈ Omega) (i : Fin 4) : (WFam i).map (conjL (castR S) (castR (cinv S))) ≤ WFam i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzRealRepDirect`.
--
--   `BookProof.ChapterLorentzRealRepDirect.WFam_conj_invariant` (S : Matrix (Fin 4) (Fin 4) ℤ) (hS : S ∈ Omega) (i : Fin 4) : (WFam i).map (conjL (castR S) (castR (cinv S))) ≤ WFam i
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLorentzRealRepDirect.WFam_conj_invariant`.

-- Generated from ChapterLorentzRealRepDirect.lean — theorem BookProof.ChapterLorentzRealRepDirect.WFam_conj_invariant
import Definitions.Def_ChapterLorentzRealRepSum
import Definitions.Def_ChapterLorentzRealRepFull
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinOmega
import Mathlib
import Definitions.Def_ChapterLorentzRealRepDirect
import Definitions.Def_ChapterLorentzRealRep
import Definitions.Def_ChapterPinDoubleCover
open BookProof.ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRepDirect


open Matrix Module


open BookProof.ChapterLorentzRealRep BookProof.ChapterLorentzRealRepSum
open BookProof.ChapterLorentzRealRepFull
open BookProof.ChapterA3 BookProof.ChapterPinOmega

theorem BookProof.ChapterLorentzRealRepDirect.WFam_conj_invariant (S : Matrix (Fin 4) (Fin 4) ℤ) (hS : S ∈ Omega) (i : Fin 4) :
    (WFam i).map (conjL (castR S) (castR (cinv S))) ≤ WFam i := by sorry
