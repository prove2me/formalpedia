-- Prove2me | Theorems.Thm_BookProof_UnboundedSpectralModel_op_resOp_inc
-- name    : BookProof.UnboundedSpectralModel.op_resOp_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T14:00:11.862123+00:00
-- url     : https://prove2.me/theorems/718726b6-861a-439d-b2c9-bda7be7ab3be
-- title:
--   `BookProof.UnboundedSpectralModel.op_resOp_inc` (T : UnboundedSelfAdjoint H) (y : H) : T.op ⟨resOp T y, resOp_mem T y⟩ = y + Complex.I • resOp T y
-- statement:
--   Prove the following Lean 4 theorem from `ChapterUnboundedSpectralModel`.
--
--   `BookProof.UnboundedSpectralModel.op_resOp_inc` (T : UnboundedSelfAdjoint H) (y : H) : T.op ⟨resOp T y, resOp_mem T y⟩ = y + Complex.I • resOp T y
--
--   Formalization note: Lean 4 identifier `BookProof.UnboundedSpectralModel.op_resOp_inc`.
--
--   Replaces the unuploadable node `BookProof_UnboundedSpectralModel_op_resOp`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.

-- Generated from ChapterUnboundedSpectralModel.lean — theorem BookProof.UnboundedSpectralModel.op_resOp_inc
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

theorem BookProof.UnboundedSpectralModel.op_resOp_inc (T : UnboundedSelfAdjoint H) (y : H) :
    T.op ⟨resOp T y, resOp_mem T y⟩ = y + Complex.I • resOp T y := by sorry
