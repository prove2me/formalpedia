-- Prove2me | Theorems.Thm_BookProof_ChapterCayleySpectralModel_cfcHom_opSymbol
-- name    : BookProof.ChapterCayleySpectralModel.cfcHom_opSymbol
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:37:50.45953+00:00
-- url     : https://prove2.me/theorems/0aae00c4-f6a5-439c-b330-5b697d739cad
-- title:
--   `BookProof.ChapterCayleySpectralModel.cfcHom_opSymbol` (y : H) : cfcHom (isStarNormal_cayleyCLM T) (opSymbol T) y = T.op (T.res (-1) y)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCayleySpectralModel`.
--
--   `BookProof.ChapterCayleySpectralModel.cfcHom_opSymbol` (y : H) : cfcHom (isStarNormal_cayleyCLM T) (opSymbol T) y = T.op (T.res (-1) y)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCayleySpectralModel.cfcHom_opSymbol`.

-- Generated from ChapterCayleySpectralModel.lean — theorem BookProof.ChapterCayleySpectralModel.cfcHom_opSymbol
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

theorem BookProof.ChapterCayleySpectralModel.cfcHom_opSymbol (y : H) :
    cfcHom (isStarNormal_cayleyCLM T) (opSymbol T) y = T.op (T.res (-1) y) := by sorry
