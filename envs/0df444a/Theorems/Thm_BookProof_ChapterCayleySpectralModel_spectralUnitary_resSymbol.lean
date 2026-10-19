-- Prove2me | Theorems.Thm_BookProof_ChapterCayleySpectralModel_spectralUnitary_resSymbol
-- name    : BookProof.ChapterCayleySpectralModel.spectralUnitary_resSymbol
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:37:50.416988+00:00
-- url     : https://prove2.me/theorems/34796d7f-d7b7-4259-a358-01a65710d97a
-- title:
--   `BookProof.ChapterCayleySpectralModel.spectralUnitary_resSymbol` (hcyc : DenseRange (cfcVec (cayleyCLM T) (isStarNormal_cayleyCLM T) xi)) (u : Lp ℂ 2 (spectralMeasure (cayleyCLM T)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCayleySpectralModel`.
--
--   `BookProof.ChapterCayleySpectralModel.spectralUnitary_resSymbol` (hcyc : DenseRange (cfcVec (cayleyCLM T) (isStarNormal_cayleyCLM T) xi)) (u : Lp ℂ 2 (spectralMeasure (cayleyCLM T) (isStarNormal_cayleyCLM T) xi)) : spectralUnitary (cayleyCLM T) (isStarNormal_cayleyCLM T) xi hcyc (mulRep (spectralMeasure (cayleyCLM T) (isStarNormal_cayleyCLM T) xi) (resSymbol T) u) = ((T.res (-1) (spectralUnitary (cayleyCLM T) (isStarNormal_cayleyCLM T) xi hcyc u) : T.domain) : H)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCayleySpectralModel.spectralUnitary_resSymbol`.

-- Generated from ChapterCayleySpectralModel.lean — theorem BookProof.ChapterCayleySpectralModel.spectralUnitary_resSymbol
import Definitions.Def_ChapterUnitaryTransport
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterCayleyTransform
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterSpectralMultiplication
import Mathlib
import Definitions.Def_ChapterCayleySpectralModel
import Definitions.Def_ChapterStoneResolvent
open BookProof.ChapterCayleySpectralModel


open scoped InnerProductSpace
open MeasureTheory


open BookProof.ChapterUnitaryTransport BookProof.ChapterStoneResolvent
open BookProof.ChapterCayleyTransform BookProof.ChapterAbelianGelfandModel
open BookProof.ChapterSpectralMultiplication

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H)

variable (xi : H)

theorem BookProof.ChapterCayleySpectralModel.spectralUnitary_resSymbol
    (hcyc : DenseRange (cfcVec (cayleyCLM T) (isStarNormal_cayleyCLM T) xi))
    (u : Lp ℂ 2 (spectralMeasure (cayleyCLM T) (isStarNormal_cayleyCLM T) xi)) :
    spectralUnitary (cayleyCLM T) (isStarNormal_cayleyCLM T) xi hcyc
        (mulRep (spectralMeasure (cayleyCLM T) (isStarNormal_cayleyCLM T) xi) (resSymbol T) u)
      = ((T.res (-1) (spectralUnitary (cayleyCLM T) (isStarNormal_cayleyCLM T) xi hcyc u) :
          T.domain) : H) := by sorry
