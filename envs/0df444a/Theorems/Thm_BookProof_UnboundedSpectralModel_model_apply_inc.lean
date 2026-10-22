-- Prove2me | Theorems.Thm_BookProof_UnboundedSpectralModel_model_apply_inc
-- name    : BookProof.UnboundedSpectralModel.model_apply_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T14:00:18.659666+00:00
-- url     : https://prove2.me/theorems/2ea287fe-0b06-4746-bfca-e98520673f56
-- title:
--   `BookProof.UnboundedSpectralModel.model_apply_inc` (u : Lp ℂ 2 mu) : T.op ⟨V (mulRep mu (coordFn (resOp T)) u), model_mem T V hV u⟩ = V (u + Complex.I • mulRep mu (coordFn (resOp T)) u
-- statement:
--   Prove the following Lean 4 theorem from `ChapterUnboundedSpectralModel`.
--
--   `BookProof.UnboundedSpectralModel.model_apply_inc` (u : Lp ℂ 2 mu) : T.op ⟨V (mulRep mu (coordFn (resOp T)) u), model_mem T V hV u⟩ = V (u + Complex.I • mulRep mu (coordFn (resOp T)) u)
--
--   Formalization note: Lean 4 identifier `BookProof.UnboundedSpectralModel.model_apply_inc`.
--
--   Replaces the unuploadable node `BookProof_UnboundedSpectralModel_model_apply`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.

-- Generated from ChapterUnboundedSpectralModel.lean — theorem BookProof.UnboundedSpectralModel.model_apply_inc
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

theorem BookProof.UnboundedSpectralModel.model_apply_inc (u : Lp ℂ 2 mu) :
    T.op ⟨V (mulRep mu (coordFn (resOp T)) u), model_mem T V hV u⟩
      = V (u + Complex.I • mulRep mu (coordFn (resOp T)) u) := by sorry
