-- Prove2me | Theorems.Thm_BookProof_ChapterSpectralDirectSum_one_lt_dist_of_orthogonalCyclicFamily
-- name    : BookProof.ChapterSpectralDirectSum.one_lt_dist_of_orthogonalCyclicFamily
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T02:16:14.894689+00:00
-- url     : https://prove2.me/theorems/31c239a9-25b8-4583-8668-8273a985f057
-- title:
--   `BookProof.ChapterSpectralDirectSum.one_lt_dist_of_orthogonalCyclicFamily` {S : Set H} (hS : OrthogonalCyclicFamily T hT S) {x y : H} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) : 1 <
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSpectralDirectSum`.
--
--   `BookProof.ChapterSpectralDirectSum.one_lt_dist_of_orthogonalCyclicFamily` {S : Set H} (hS : OrthogonalCyclicFamily T hT S) {x y : H} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) : 1 < dist x y
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSpectralDirectSum.one_lt_dist_of_orthogonalCyclicFamily`.

-- Generated from ChapterSpectralDirectSum.lean — theorem BookProof.ChapterSpectralDirectSum.one_lt_dist_of_orthogonalCyclicFamily
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

theorem BookProof.ChapterSpectralDirectSum.one_lt_dist_of_orthogonalCyclicFamily {S : Set H} (hS : OrthogonalCyclicFamily T hT S)
    {x y : H} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) : 1 < dist x y := by sorry
