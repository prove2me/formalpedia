-- Prove2me | Theorems.Thm_BookProof_UnboundedSpectralModel_model_ae_ne_zero_inc
-- name    : BookProof.UnboundedSpectralModel.model_ae_ne_zero_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T14:00:26.992106+00:00
-- url     : https://prove2.me/theorems/1f63690b-bc19-4cc1-be1f-3559c00ff559
-- title:
--   `BookProof.UnboundedSpectralModel.model_ae_ne_zero_inc` [IsFiniteMeasure mu] : ∀ᵐ z ∂mu, z.1 ≠ 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterUnboundedSpectralModel`.
--
--   `BookProof.UnboundedSpectralModel.model_ae_ne_zero_inc` [IsFiniteMeasure mu] : ∀ᵐ z ∂mu, z.1 ≠ 0
--
--   Formalization note: Lean 4 identifier `BookProof.UnboundedSpectralModel.model_ae_ne_zero_inc`.
--
--   Replaces the unuploadable node `BookProof_UnboundedSpectralModel_model_ae_ne_zero`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.

-- Generated from ChapterUnboundedSpectralModel.lean — theorem BookProof.UnboundedSpectralModel.model_ae_ne_zero_inc
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

theorem BookProof.UnboundedSpectralModel.model_ae_ne_zero_inc [IsFiniteMeasure mu] : ∀ᵐ z ∂mu, z.1 ≠ 0 := by sorry
