-- Prove2me | Theorems.Thm_BookProof_UnboundedSpectralModel_resOp_injective_inc
-- name    : BookProof.UnboundedSpectralModel.resOp_injective_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T14:00:40.506627+00:00
-- url     : https://prove2.me/theorems/92998885-2ee4-417d-ae3c-43a6171aa8c0
-- title:
--   `BookProof.UnboundedSpectralModel.resOp_injective_inc` (T : UnboundedSelfAdjoint H) : Function.Injective (resOp T)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterUnboundedSpectralModel`.
--
--   `BookProof.UnboundedSpectralModel.resOp_injective_inc` (T : UnboundedSelfAdjoint H) : Function.Injective (resOp T)
--
--   Formalization note: Lean 4 identifier `BookProof.UnboundedSpectralModel.resOp_injective_inc`.
--
--   Replaces the unuploadable node `BookProof_UnboundedSpectralModel_resOp_injective`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.

-- Generated from ChapterUnboundedSpectralModel.lean — theorem BookProof.UnboundedSpectralModel.resOp_injective_inc
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

theorem BookProof.UnboundedSpectralModel.resOp_injective_inc (T : UnboundedSelfAdjoint H) : Function.Injective (resOp T) := by sorry
