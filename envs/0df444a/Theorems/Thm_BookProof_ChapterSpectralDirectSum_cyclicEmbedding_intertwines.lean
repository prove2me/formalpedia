-- Prove2me | Theorems.Thm_BookProof_ChapterSpectralDirectSum_cyclicEmbedding_intertwines
-- name    : BookProof.ChapterSpectralDirectSum.cyclicEmbedding_intertwines
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T02:15:25.150988+00:00
-- url     : https://prove2.me/theorems/8ecebc8e-68f6-4c40-a5ab-aabffc1d806a
-- title:
--   `BookProof.ChapterSpectralDirectSum.cyclicEmbedding_intertwines` (u : Lp ℂ 2 (spectralMeasure T hT xi)) : cyclicEmbedding T hT xi (mulRep (spectralMeasure T hT xi) (coordFn T) u) =
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSpectralDirectSum`.
--
--   `BookProof.ChapterSpectralDirectSum.cyclicEmbedding_intertwines` (u : Lp ℂ 2 (spectralMeasure T hT xi)) : cyclicEmbedding T hT xi (mulRep (spectralMeasure T hT xi) (coordFn T) u) = T (cyclicEmbedding T hT xi u)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSpectralDirectSum.cyclicEmbedding_intertwines`.

-- Generated from ChapterSpectralDirectSum.lean — theorem BookProof.ChapterSpectralDirectSum.cyclicEmbedding_intertwines
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

theorem BookProof.ChapterSpectralDirectSum.cyclicEmbedding_intertwines (u : Lp ℂ 2 (spectralMeasure T hT xi)) :
    cyclicEmbedding T hT xi (mulRep (spectralMeasure T hT xi) (coordFn T) u)
      = T (cyclicEmbedding T hT xi u) := by sorry
