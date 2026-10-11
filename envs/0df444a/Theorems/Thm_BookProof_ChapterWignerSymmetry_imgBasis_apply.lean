-- Prove2me | Theorems.Thm_BookProof_ChapterWignerSymmetry_imgBasis_apply
-- name    : BookProof.ChapterWignerSymmetry.imgBasis_apply
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T18:19:35.159349+00:00
-- url     : https://prove2.me/theorems/035fb041-c74b-46db-806d-0dcecbf8fe0f
-- title:
--   `BookProof.ChapterWignerSymmetry.imgBasis_apply` (hT : IsWignerSymmetry T) (i : ι) : imgBasis b T o hT i = alignPhase b T o i • T (b i)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerSymmetry`.
--
--   `BookProof.ChapterWignerSymmetry.imgBasis_apply` (hT : IsWignerSymmetry T) (i : ι) : imgBasis b T o hT i = alignPhase b T o i • T (b i)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerSymmetry.imgBasis_apply`.

-- Generated from ChapterWignerSymmetry.lean — theorem BookProof.ChapterWignerSymmetry.imgBasis_apply
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

theorem BookProof.ChapterWignerSymmetry.imgBasis_apply (hT : IsWignerSymmetry T) (i : ι) :
    imgBasis b T o hT i = alignPhase b T o i • T (b i) := by sorry
