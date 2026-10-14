-- Prove2me | Theorems.Thm_BookProof_ChapterWignerSymmetry_sum_pairCoord
-- name    : BookProof.ChapterWignerSymmetry.sum_pairCoord
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T18:19:25.657546+00:00
-- url     : https://prove2.me/theorems/411c201d-67ae-46ea-9b4c-1f09a83f4279
-- title:
--   `BookProof.ChapterWignerSymmetry.sum_pairCoord` (b : OrthonormalBasis ι ℂ E) {o i : ι} (hi : i ≠ o) : ∑ j, pairCoord o i j • b j = b o + b i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerSymmetry`.
--
--   `BookProof.ChapterWignerSymmetry.sum_pairCoord` (b : OrthonormalBasis ι ℂ E) {o i : ι} (hi : i ≠ o) : ∑ j, pairCoord o i j • b j = b o + b i
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerSymmetry.sum_pairCoord`.

-- Generated from ChapterWignerSymmetry.lean — theorem BookProof.ChapterWignerSymmetry.sum_pairCoord
import Mathlib
import Definitions.Def_ChapterWignerSymmetry
open BookProof.ChapterWignerSymmetry


open scoped InnerProductSpace ComplexConjugate
open Finset


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


variable {T : E → E}

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : (ι → ℂ) → (ι → ℂ)} {o : ι}

theorem BookProof.ChapterWignerSymmetry.sum_pairCoord (b : OrthonormalBasis ι ℂ E) {o i : ι} (hi : i ≠ o) :
    ∑ j, pairCoord o i j • b j = b o + b i := by sorry
