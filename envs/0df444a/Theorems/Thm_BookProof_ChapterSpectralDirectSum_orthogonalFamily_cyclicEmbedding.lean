-- Prove2me | Theorems.Thm_BookProof_ChapterSpectralDirectSum_orthogonalFamily_cyclicEmbedding
-- name    : BookProof.ChapterSpectralDirectSum.orthogonalFamily_cyclicEmbedding
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T02:15:30.468486+00:00
-- url     : https://prove2.me/theorems/c0151cb2-c140-4ec2-9400-b3b49c9554bd
-- title:
--   `BookProof.ChapterSpectralDirectSum.orthogonalFamily_cyclicEmbedding` {S : Set H} (hS : OrthogonalCyclicFamily T hT S) : OrthogonalFamily ℂ (fun x : S => Lp ℂ 2 (spectralMeasure T
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSpectralDirectSum`.
--
--   `BookProof.ChapterSpectralDirectSum.orthogonalFamily_cyclicEmbedding` {S : Set H} (hS : OrthogonalCyclicFamily T hT S) : OrthogonalFamily ℂ (fun x : S => Lp ℂ 2 (spectralMeasure T hT (x : H))) (fun x : S => cyclicEmbedding T hT (x : H))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSpectralDirectSum.orthogonalFamily_cyclicEmbedding`.

-- Generated from ChapterSpectralDirectSum.lean — theorem BookProof.ChapterSpectralDirectSum.orthogonalFamily_cyclicEmbedding
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

theorem BookProof.ChapterSpectralDirectSum.orthogonalFamily_cyclicEmbedding {S : Set H} (hS : OrthogonalCyclicFamily T hT S) :
    OrthogonalFamily ℂ (fun x : S => Lp ℂ 2 (spectralMeasure T hT (x : H)))
      (fun x : S => cyclicEmbedding T hT (x : H)) := by sorry
