-- Prove2me | Theorems.Thm_BookProof_ChapterCayleySpectralModel_cfcHom_resSymbol
-- name    : BookProof.ChapterCayleySpectralModel.cfcHom_resSymbol
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:37:25.381956+00:00
-- url     : https://prove2.me/theorems/e9341355-0148-4cc3-84f9-e9a94c820a2b
-- title:
--   `BookProof.ChapterCayleySpectralModel.cfcHom_resSymbol` (y : H) : cfcHom (isStarNormal_cayleyCLM T) (resSymbol T) y = ((T.res (-1) y : T.domain) : H)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCayleySpectralModel`.
--
--   `BookProof.ChapterCayleySpectralModel.cfcHom_resSymbol` (y : H) : cfcHom (isStarNormal_cayleyCLM T) (resSymbol T) y = ((T.res (-1) y : T.domain) : H)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCayleySpectralModel.cfcHom_resSymbol`.

-- Generated from ChapterCayleySpectralModel.lean — theorem BookProof.ChapterCayleySpectralModel.cfcHom_resSymbol
import Definitions.Def_ChapterUnitaryTransport
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterSpectralMultiplication
import Mathlib
import Definitions.Def_ChapterCayleySpectralModel
import Definitions.Def_ChapterCayleyTransform
import Definitions.Def_ChapterStoneResolvent
open BookProof.ChapterCayleyTransform
open BookProof.ChapterCayleySpectralModel


open scoped InnerProductSpace
open MeasureTheory


open BookProof.ChapterUnitaryTransport BookProof.ChapterStoneResolvent
open BookProof.ChapterCayleyTransform BookProof.ChapterAbelianGelfandModel
open BookProof.ChapterSpectralMultiplication

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H)

theorem BookProof.ChapterCayleySpectralModel.cfcHom_resSymbol (y : H) :
    cfcHom (isStarNormal_cayleyCLM T) (resSymbol T) y = ((T.res (-1) y : T.domain) : H) := by sorry
