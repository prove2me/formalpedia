-- Prove2me | Theorems.Thm_BookProof_ChapterLorentzRealRep_WHalf_invariant_apply
-- name    : BookProof.ChapterLorentzRealRep.WHalf_invariant_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:38:42.438991+00:00
-- url     : https://prove2.me/theorems/e3b9ef9a-0d2b-4d6a-9262-187cefee4c5c
-- title:
--   `BookProof.ChapterLorentzRealRep.WHalf_invariant_apply` (S : Matrix (Fin 4) (Fin 4) ℤ) (hS : S ∈ Omega) (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A ∈ WHalf) : castR S * A * castR (cinv
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLorentzRealRep`.
--
--   `BookProof.ChapterLorentzRealRep.WHalf_invariant_apply` (S : Matrix (Fin 4) (Fin 4) ℤ) (hS : S ∈ Omega) (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A ∈ WHalf) : castR S * A * castR (cinv S) ∈ WHalf
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLorentzRealRep.WHalf_invariant_apply`.

-- Generated from ChapterLorentzRealRep.lean — theorem BookProof.ChapterLorentzRealRep.WHalf_invariant_apply
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinOmega
import Mathlib
import Definitions.Def_ChapterLorentzRealRep
import Definitions.Def_ChapterPinDoubleCover
open BookProof.ChapterLorentzRealRep


open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega

theorem BookProof.ChapterLorentzRealRep.WHalf_invariant_apply (S : Matrix (Fin 4) (Fin 4) ℤ) (hS : S ∈ Omega)
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A ∈ WHalf) :
    castR S * A * castR (cinv S) ∈ WHalf := by sorry
