-- Prove2me | Theorems.Thm_BookProof_ChapterSpectralDirectSum_inner_eq_zero_of_orthogonalCyclicFamily
-- name    : BookProof.ChapterSpectralDirectSum.inner_eq_zero_of_orthogonalCyclicFamily
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T02:15:57.136241+00:00
-- url     : https://prove2.me/theorems/9bde69eb-6141-4dd4-b6bb-5d85127b0d8f
-- title:
--   `BookProof.ChapterSpectralDirectSum.inner_eq_zero_of_orthogonalCyclicFamily` {S : Set H} (hS : OrthogonalCyclicFamily T hT S) {x y : H} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) : in
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSpectralDirectSum`.
--
--   `BookProof.ChapterSpectralDirectSum.inner_eq_zero_of_orthogonalCyclicFamily` {S : Set H} (hS : OrthogonalCyclicFamily T hT S) {x y : H} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) : inner ℂ x y = (0 : ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSpectralDirectSum.inner_eq_zero_of_orthogonalCyclicFamily`.

-- Generated from ChapterSpectralDirectSum.lean — theorem BookProof.ChapterSpectralDirectSum.inner_eq_zero_of_orthogonalCyclicFamily
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterSpectralMultiplication
import Definitions.Def_ChapterCyclicDecomposition
import Definitions.Def_ChapterCyclicDirectSum
import Mathlib
import Definitions.Def_ChapterSpectralDirectSum
open BookProof.ChapterSpectralDirectSum


noncomputable section

open MeasureTheory Complex


open BookProof.ChapterAbelianGelfandModel BookProof.ChapterSpectralMultiplication
open BookProof.ChapterCyclicDecomposition BookProof.ChapterCyclicDirectSum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) (hT : IsStarNormal T) (xi : H)

theorem BookProof.ChapterSpectralDirectSum.inner_eq_zero_of_orthogonalCyclicFamily {S : Set H} (hS : OrthogonalCyclicFamily T hT S)
    {x y : H} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) : inner ℂ x y = (0 : ℂ) := by sorry
