-- Prove2me | Theorems.Thm_BookProof_UnboundedSpectralModel_mulRep_cayleyFn_eq_zero_inc
-- name    : BookProof.UnboundedSpectralModel.mulRep_cayleyFn_eq_zero_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T13:59:58.380278+00:00
-- url     : https://prove2.me/theorems/51918e95-7a4f-47e5-9130-f07599f0d0ba
-- title:
--   `BookProof.UnboundedSpectralModel.mulRep_cayleyFn_eq_zero_inc` [IsFiniteMeasure mu] : mulRep mu (cayleyFn T) = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterUnboundedSpectralModel`.
--
--   `BookProof.UnboundedSpectralModel.mulRep_cayleyFn_eq_zero_inc` [IsFiniteMeasure mu] : mulRep mu (cayleyFn T) = 0
--
--   Formalization note: Lean 4 identifier `BookProof.UnboundedSpectralModel.mulRep_cayleyFn_eq_zero_inc`.
--
--   Replaces the unuploadable node `BookProof_UnboundedSpectralModel_mulRep_cayleyFn_eq_zero`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.

-- Generated from ChapterUnboundedSpectralModel.lean — theorem BookProof.UnboundedSpectralModel.mulRep_cayleyFn_eq_zero_inc
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

variable (T : UnboundedSelfAdjoint H) {mu : Measure (spectrum ℂ (resOp T))}
  (V : Lp ℂ 2 mu →ₗᵢ[ℂ] H)
  (hV : ∀ u : Lp ℂ 2 mu, V (mulRep mu (coordFn (resOp T)) u) = resOp T (V u))

include hV in

theorem BookProof.UnboundedSpectralModel.mulRep_cayleyFn_eq_zero_inc [IsFiniteMeasure mu] : mulRep mu (cayleyFn T) = 0 := by sorry
