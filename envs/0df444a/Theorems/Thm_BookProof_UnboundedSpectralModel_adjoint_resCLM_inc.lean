-- Prove2me | Theorems.Thm_BookProof_UnboundedSpectralModel_adjoint_resCLM_inc
-- name    : BookProof.UnboundedSpectralModel.adjoint_resCLM_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T13:59:43.319692+00:00
-- url     : https://prove2.me/theorems/fb9fe1de-e973-4de1-a37b-d44de59c5f4e
-- title:
--   `BookProof.UnboundedSpectralModel.adjoint_resCLM_inc` (T : UnboundedSelfAdjoint H) {l : ℝ} (hl : l ≠ 0) : ContinuousLinearMap.adjoint (T.resCLM l) = T.resCLM (-l)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterUnboundedSpectralModel`.
--
--   `BookProof.UnboundedSpectralModel.adjoint_resCLM_inc` (T : UnboundedSelfAdjoint H) {l : ℝ} (hl : l ≠ 0) : ContinuousLinearMap.adjoint (T.resCLM l) = T.resCLM (-l)
--
--   Formalization note: Lean 4 identifier `BookProof.UnboundedSpectralModel.adjoint_resCLM_inc`.
--
--   Replaces the unuploadable node `BookProof_UnboundedSpectralModel_adjoint_resCLM`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.

-- Generated from ChapterUnboundedSpectralModel.lean — theorem BookProof.UnboundedSpectralModel.adjoint_resCLM_inc
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

theorem BookProof.UnboundedSpectralModel.adjoint_resCLM_inc (T : UnboundedSelfAdjoint H) {l : ℝ} (hl : l ≠ 0) :
    ContinuousLinearMap.adjoint (T.resCLM l) = T.resCLM (-l) := by sorry
