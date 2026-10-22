-- Prove2me | Theorems.Thm_BookProof_UnboundedSpectralModel_resOp_mem_inc
-- name    : BookProof.UnboundedSpectralModel.resOp_mem_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T14:00:05.667669+00:00
-- url     : https://prove2.me/theorems/71faede0-80e6-4702-9fdf-731a0f5d010a
-- title:
--   `BookProof.UnboundedSpectralModel.resOp_mem_inc` (T : UnboundedSelfAdjoint H) (y : H) : resOp T y ∈ T.domain
-- statement:
--   Prove the following Lean 4 theorem from `ChapterUnboundedSpectralModel`.
--
--   `BookProof.UnboundedSpectralModel.resOp_mem_inc` (T : UnboundedSelfAdjoint H) (y : H) : resOp T y ∈ T.domain
--
--   Formalization note: Lean 4 identifier `BookProof.UnboundedSpectralModel.resOp_mem_inc`.
--
--   Replaces the unuploadable node `BookProof_UnboundedSpectralModel_resOp_mem`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.

-- Generated from ChapterUnboundedSpectralModel.lean — theorem BookProof.UnboundedSpectralModel.resOp_mem_inc
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

theorem BookProof.UnboundedSpectralModel.resOp_mem_inc (T : UnboundedSelfAdjoint H) (y : H) : resOp T y ∈ T.domain := by sorry
