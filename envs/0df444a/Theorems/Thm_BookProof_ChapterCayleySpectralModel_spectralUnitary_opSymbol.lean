-- Prove2me | Theorems.Thm_BookProof_ChapterCayleySpectralModel_spectralUnitary_opSymbol
-- name    : BookProof.ChapterCayleySpectralModel.spectralUnitary_opSymbol
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:38:01.027978+00:00
-- url     : https://prove2.me/theorems/8532819d-a75c-4eb5-9d28-5078fa43f786
-- title:
--   `BookProof.ChapterCayleySpectralModel.spectralUnitary_opSymbol` (hcyc : DenseRange (cfcVec (cayleyCLM T) (isStarNormal_cayleyCLM T) xi)) (u : Lp ℂ 2 (spectralMeasure (cayleyCLM T)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCayleySpectralModel`.
--
--   `BookProof.ChapterCayleySpectralModel.spectralUnitary_opSymbol` (hcyc : DenseRange (cfcVec (cayleyCLM T) (isStarNormal_cayleyCLM T) xi)) (u : Lp ℂ 2 (spectralMeasure (cayleyCLM T) (isStarNormal_cayleyCLM T) xi)) : spectralUnitary (cayleyCLM T) (isStarNormal_cayleyCLM T) xi hcyc (mulRep (spectralMeasure (cayleyCLM T) (isStarNormal_cayleyCLM T) xi) (opSymbol T) u) = T.op (T.res (-1) (spectralUnitary (cayleyCLM T) (isStarNormal_cayleyCLM T) xi hcyc u))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCayleySpectralModel.spectralUnitary_opSymbol`.

-- Generated from ChapterCayleySpectralModel.lean — theorem BookProof.ChapterCayleySpectralModel.spectralUnitary_opSymbol
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

theorem BookProof.ChapterCayleySpectralModel.spectralUnitary_opSymbol
    (hcyc : DenseRange (cfcVec (cayleyCLM T) (isStarNormal_cayleyCLM T) xi))
    (u : Lp ℂ 2 (spectralMeasure (cayleyCLM T) (isStarNormal_cayleyCLM T) xi)) :
    spectralUnitary (cayleyCLM T) (isStarNormal_cayleyCLM T) xi hcyc
        (mulRep (spectralMeasure (cayleyCLM T) (isStarNormal_cayleyCLM T) xi) (opSymbol T) u)
      = T.op (T.res (-1) (spectralUnitary (cayleyCLM T) (isStarNormal_cayleyCLM T) xi hcyc u)) := by sorry
