-- Prove2me | Theorems.Thm_BookProof_ChapterWeylSl2_Sl2Rep_isInv_scalarOps
-- name    : BookProof.ChapterWeylSl2.Sl2Rep.isInv_scalarOps
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T20:40:54.174686+00:00
-- url     : https://prove2.me/theorems/b3ae90ce-7a81-402f-ac88-de143749d584
-- title:
--   `BookProof.ChapterWeylSl2.Sl2Rep.isInv_scalarOps` {R : Sl2Rep V} {W : Submodule ℂ V} (hW : R.IsInv W) : (adRep R).IsInv (scalarOps W)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylSl2`.
--
--   `BookProof.ChapterWeylSl2.Sl2Rep.isInv_scalarOps` {R : Sl2Rep V} {W : Submodule ℂ V} (hW : R.IsInv W) : (adRep R).IsInv (scalarOps W)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWeylSl2.Sl2Rep.isInv_scalarOps`.

-- Generated from ChapterWeylSl2.lean — theorem BookProof.ChapterWeylSl2.Sl2Rep.isInv_scalarOps
import Mathlib
import Definitions.Def_ChapterWeylSl2
import Definitions.Def_ChapterDoubleSlit
import Definitions.Def_ChapterGleasonPureMixed
open BookProof.ChapterDoubleSlit
open BookProof.ChapterGleasonPureMixed
open BookProof.ChapterWeylSl2
open BookProof.ChapterWeylSl2



universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

variable (R : Sl2Rep V)
variable {R}
variable {R : Sl2Rep V}

theorem BookProof.ChapterWeylSl2.Sl2Rep.isInv_scalarOps {R : Sl2Rep V} {W : Submodule ℂ V} (hW : R.IsInv W) :
    (adRep R).IsInv (scalarOps W) := by sorry
