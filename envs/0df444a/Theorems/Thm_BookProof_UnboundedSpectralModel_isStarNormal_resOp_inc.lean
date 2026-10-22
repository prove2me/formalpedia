-- Prove2me | Theorems.Thm_BookProof_UnboundedSpectralModel_isStarNormal_resOp_inc
-- name    : BookProof.UnboundedSpectralModel.isStarNormal_resOp_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T13:59:51.277427+00:00
-- url     : https://prove2.me/theorems/14082e30-581b-4cff-abf8-2fec60bd9e05
-- title:
--   `BookProof.UnboundedSpectralModel.isStarNormal_resOp_inc` (T : UnboundedSelfAdjoint H) : IsStarNormal (resOp T)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterUnboundedSpectralModel`.
--
--   `BookProof.UnboundedSpectralModel.isStarNormal_resOp_inc` (T : UnboundedSelfAdjoint H) : IsStarNormal (resOp T)
--
--   Formalization note: Lean 4 identifier `BookProof.UnboundedSpectralModel.isStarNormal_resOp_inc`.
--
--   Replaces the unuploadable node `BookProof_UnboundedSpectralModel_isStarNormal_resOp`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.

-- Generated from ChapterUnboundedSpectralModel.lean — theorem BookProof.UnboundedSpectralModel.isStarNormal_resOp_inc
import Definitions.Def_ChapterUnitaryTransport
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterSpectralMultiplication
import Definitions.Def_ChapterSpectralDirectSum
import Mathlib
import Definitions.Def_ChapterUnboundedSpectralModel
import Definitions.Def_ChapterStoneResolvent
open BookProof.UnboundedSpectralModel


noncomputable section

open MeasureTheory Complex
open scoped InnerProductSpace


open BookProof.ChapterUnitaryTransport BookProof.ChapterStoneResolvent
open BookProof.ChapterAbelianGelfandModel BookProof.ChapterSpectralMultiplication
open BookProof.ChapterSpectralDirectSum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem BookProof.UnboundedSpectralModel.isStarNormal_resOp_inc (T : UnboundedSelfAdjoint H) : IsStarNormal (resOp T) := by sorry
