-- Prove2me | Theorems.Thm_BookProof_UnboundedSpectralModel_model_symmetry_relation_inc
-- name    : BookProof.UnboundedSpectralModel.model_symmetry_relation_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T14:00:24.727959+00:00
-- url     : https://prove2.me/theorems/943793fd-f39a-4c29-abdc-ecbd4d088a04
-- title:
--   `BookProof.UnboundedSpectralModel.model_symmetry_relation_inc` (u : Lp ℂ 2 mu) : (inner ℂ u (mulRep mu (coordFn (resOp T)) u) : ℂ) - inner ℂ (mulRep mu (coordFn (resOp T)) u) u = (2 *
-- statement:
--   Prove the following Lean 4 theorem from `ChapterUnboundedSpectralModel`.
--
--   `BookProof.UnboundedSpectralModel.model_symmetry_relation_inc` (u : Lp ℂ 2 mu) : (inner ℂ u (mulRep mu (coordFn (resOp T)) u) : ℂ) - inner ℂ (mulRep mu (coordFn (resOp T)) u) u = (2 * Complex.I) * inner ℂ (mulRep mu (coordFn (resOp T)) u) (mulRep mu (coordFn (resOp T)) u)
--
--   Formalization note: Lean 4 identifier `BookProof.UnboundedSpectralModel.model_symmetry_relation_inc`.
--
--   Replaces the unuploadable node `BookProof_UnboundedSpectralModel_model_symmetry_relation`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.

-- Generated from ChapterUnboundedSpectralModel.lean — theorem BookProof.UnboundedSpectralModel.model_symmetry_relation_inc
import Definitions.Def_ChapterUnitaryTransport
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterSpectralMultiplication
import Definitions.Def_ChapterSpectralDirectSum
import Mathlib
import Definitions.Def_ChapterUnboundedSpectralModel
import Definitions.Def_ChapterStoneConverse
import Definitions.Def_ChapterStoneResolvent
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup
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

theorem BookProof.UnboundedSpectralModel.model_symmetry_relation_inc (u : Lp ℂ 2 mu) :
    (inner ℂ u (mulRep mu (coordFn (resOp T)) u) : ℂ)
        - inner ℂ (mulRep mu (coordFn (resOp T)) u) u
      = (2 * Complex.I)
          * inner ℂ (mulRep mu (coordFn (resOp T)) u) (mulRep mu (coordFn (resOp T)) u) := by sorry
