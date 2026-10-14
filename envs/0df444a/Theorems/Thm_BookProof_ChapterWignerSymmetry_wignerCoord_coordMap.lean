-- Prove2me | Theorems.Thm_BookProof_ChapterWignerSymmetry_wignerCoord_coordMap
-- name    : BookProof.ChapterWignerSymmetry.wignerCoord_coordMap
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T18:19:40.338023+00:00
-- url     : https://prove2.me/theorems/797cf535-78f0-4cb9-9013-55e96c780038
-- title:
--   `BookProof.ChapterWignerSymmetry.wignerCoord_coordMap` (hT : IsWignerSymmetry T) : WignerCoord (coordMap b T (imgBasis b T o hT)) o
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerSymmetry`.
--
--   `BookProof.ChapterWignerSymmetry.wignerCoord_coordMap` (hT : IsWignerSymmetry T) : WignerCoord (coordMap b T (imgBasis b T o hT)) o
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerSymmetry.wignerCoord_coordMap`.

-- Generated from ChapterWignerSymmetry.lean — theorem BookProof.ChapterWignerSymmetry.wignerCoord_coordMap
import Mathlib
import Definitions.Def_ChapterWignerSymmetry
open BookProof.ChapterWignerSymmetry


open scoped InnerProductSpace ComplexConjugate
open Finset


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


variable {T : E → E}

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : (ι → ℂ) → (ι → ℂ)} {o : ι}
variable {b : OrthonormalBasis ι ℂ E} {o : ι}

theorem BookProof.ChapterWignerSymmetry.wignerCoord_coordMap (hT : IsWignerSymmetry T) :
    WignerCoord (coordMap b T (imgBasis b T o hT)) o := by sorry
