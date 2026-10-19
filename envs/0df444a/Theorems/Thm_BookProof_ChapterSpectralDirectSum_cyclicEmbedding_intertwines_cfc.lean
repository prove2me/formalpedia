-- Prove2me | Theorems.Thm_BookProof_ChapterSpectralDirectSum_cyclicEmbedding_intertwines_cfc
-- name    : BookProof.ChapterSpectralDirectSum.cyclicEmbedding_intertwines_cfc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T02:15:13.501355+00:00
-- url     : https://prove2.me/theorems/636359ae-d072-4c96-ae1b-63af3556f029
-- title:
--   `BookProof.ChapterSpectralDirectSum.cyclicEmbedding_intertwines_cfc` (g : C(spectrum ℂ T, ℂ)) (u : Lp ℂ 2 (spectralMeasure T hT xi)) : cyclicEmbedding T hT xi (mulRep (spectralMeas
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSpectralDirectSum`.
--
--   `BookProof.ChapterSpectralDirectSum.cyclicEmbedding_intertwines_cfc` (g : C(spectrum ℂ T, ℂ)) (u : Lp ℂ 2 (spectralMeasure T hT xi)) : cyclicEmbedding T hT xi (mulRep (spectralMeasure T hT xi) g u) = cfcHom hT g (cyclicEmbedding T hT xi u)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSpectralDirectSum.cyclicEmbedding_intertwines_cfc`.

-- Generated from ChapterSpectralDirectSum.lean — theorem BookProof.ChapterSpectralDirectSum.cyclicEmbedding_intertwines_cfc
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

theorem BookProof.ChapterSpectralDirectSum.cyclicEmbedding_intertwines_cfc (g : C(spectrum ℂ T, ℂ))
    (u : Lp ℂ 2 (spectralMeasure T hT xi)) :
    cyclicEmbedding T hT xi (mulRep (spectralMeasure T hT xi) g u)
      = cfcHom hT g (cyclicEmbedding T hT xi u) := by sorry
