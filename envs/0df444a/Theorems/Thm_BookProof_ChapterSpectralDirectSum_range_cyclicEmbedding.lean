-- Prove2me | Theorems.Thm_BookProof_ChapterSpectralDirectSum_range_cyclicEmbedding
-- name    : BookProof.ChapterSpectralDirectSum.range_cyclicEmbedding
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T02:14:51.946077+00:00
-- url     : https://prove2.me/theorems/66031210-6d79-4a76-bbac-2b6efbe73a9d
-- title:
--   `BookProof.ChapterSpectralDirectSum.range_cyclicEmbedding` : LinearMap.range (cyclicEmbedding T hT xi).toLinearMap = cyclicSubspace T hT xi
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSpectralDirectSum`.
--
--   `BookProof.ChapterSpectralDirectSum.range_cyclicEmbedding` : LinearMap.range (cyclicEmbedding T hT xi).toLinearMap = cyclicSubspace T hT xi
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSpectralDirectSum.range_cyclicEmbedding`.

-- Generated from ChapterSpectralDirectSum.lean — theorem BookProof.ChapterSpectralDirectSum.range_cyclicEmbedding
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

theorem BookProof.ChapterSpectralDirectSum.range_cyclicEmbedding :
    LinearMap.range (cyclicEmbedding T hT xi).toLinearMap = cyclicSubspace T hT xi := by sorry
