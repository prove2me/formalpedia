-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_comm_ann_cre
-- name    : BookProof.NavierStokesFlow.FockCanonical.comm_ann_cre
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T21:53:09.876856+00:00
-- url     : https://prove2.me/theorems/877cbe6c-2d36-4b03-9043-f7b64b3718bd
-- title:
--   (i : Fin d) : (ann i).comp (cre i) - (cre i).comp (ann i) = LinearMap.id
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockCanonical.comm_ann_cre` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockCanonical.lean — theorem BookProof.NavierStokesFlow.FockCanonical.comm_ann_cre
import Mathlib
import Definitions.Def_ChapterNavierStokesFockCanonical
import Definitions.Def_ChapterBosonicCCR
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFockManyMode
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.Bosonic
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockCanonical

variable {d : ℕ} {κ : Fin d → ℝ}


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato ShiftHamiltonian FockManyMode HermiteCanonical

theorem BookProof.NavierStokesFlow.FockCanonical.comm_ann_cre (i : Fin d) :
    (ann i).comp (cre i) - (cre i).comp (ann i) = LinearMap.id := by sorry
