-- Prove2me | Theorems.Thm_BookProof_ChapterSpectralDirectSum_mem_cyclicSubspace_cyclicEmbedding
-- name    : BookProof.ChapterSpectralDirectSum.mem_cyclicSubspace_cyclicEmbedding
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T02:15:01.892032+00:00
-- url     : https://prove2.me/theorems/6c69d127-b478-4588-bdb8-7a9f4f6606b6
-- title:
--   `BookProof.ChapterSpectralDirectSum.mem_cyclicSubspace_cyclicEmbedding` (u : Lp ℂ 2 (spectralMeasure T hT xi)) : cyclicEmbedding T hT xi u ∈ cyclicSubspace T hT xi
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSpectralDirectSum`.
--
--   `BookProof.ChapterSpectralDirectSum.mem_cyclicSubspace_cyclicEmbedding` (u : Lp ℂ 2 (spectralMeasure T hT xi)) : cyclicEmbedding T hT xi u ∈ cyclicSubspace T hT xi
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSpectralDirectSum.mem_cyclicSubspace_cyclicEmbedding`.

-- Generated from ChapterSpectralDirectSum.lean — theorem BookProof.ChapterSpectralDirectSum.mem_cyclicSubspace_cyclicEmbedding
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

theorem BookProof.ChapterSpectralDirectSum.mem_cyclicSubspace_cyclicEmbedding (u : Lp ℂ 2 (spectralMeasure T hT xi)) :
    cyclicEmbedding T hT xi u ∈ cyclicSubspace T hT xi := by sorry
