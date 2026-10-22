-- Prove2me | Theorems.Thm_BookProof_UnboundedSpectralModel_unbounded_multiplication_model_cyclic_inc
-- name    : BookProof.UnboundedSpectralModel.unbounded_multiplication_model_cyclic_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T14:00:51.414187+00:00
-- url     : https://prove2.me/theorems/1baeba21-f478-4467-95ac-0f33dd7cdcf7
-- title:
--   `BookProof.UnboundedSpectralModel.unbounded_multiplication_model_cyclic_inc` (T : UnboundedSelfAdjoint H) (xi : H) (hxi : ‖xi‖ = 1) (hcyc : DenseRange (cfcVec (resOp T) (isStarNormal_r
-- statement:
--   Prove the following Lean 4 theorem from `ChapterUnboundedSpectralModel`.
--
--   `BookProof.UnboundedSpectralModel.unbounded_multiplication_model_cyclic_inc` (T : UnboundedSelfAdjoint H) (xi : H) (hxi : ‖xi‖ = 1) (hcyc : DenseRange (cfcVec (resOp T) (isStarNormal_resOp T) xi)) : ∃ (mu : Measure (spectrum ℂ (resOp T))) (_ : IsProbabilityMeasure mu) (U : Lp ℂ 2 mu ≃ₗᵢ[ℂ] H), (∀ᵐ z ∂mu, z.1 ≠ 0 ∧ ‖z.1‖ ^ 2 = z.1.im) ∧ (∀ u : Lp ℂ 2 mu, ∃ h : U (mulRep mu (coordFn (resOp T)) u) ∈ T.domain, T.op ⟨U (mulRep mu (coordFn (resOp T)) u), h⟩ = U (u + Complex.I • mulRep mu (coordFn (resOp T)) u)) ∧ (∀ x ∈ T.domain, ∃ u : Lp ℂ 2 mu, x = U (mulRep mu (coordFn (resOp T)) u))
--
--   Formalization note: Lean 4 identifier `BookProof.UnboundedSpectralModel.unbounded_multiplication_model_cyclic_inc`.
--
--   Replaces the unuploadable node `BookProof_UnboundedSpectralModel_unbounded_multiplication_model_cyclic`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.

-- Generated from ChapterUnboundedSpectralModel.lean — theorem BookProof.UnboundedSpectralModel.unbounded_multiplication_model_cyclic_inc
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

theorem BookProof.UnboundedSpectralModel.unbounded_multiplication_model_cyclic_inc (T : UnboundedSelfAdjoint H) (xi : H)
    (hxi : ‖xi‖ = 1)
    (hcyc : DenseRange (cfcVec (resOp T) (isStarNormal_resOp T) xi)) :
    ∃ (mu : Measure (spectrum ℂ (resOp T))) (_ : IsProbabilityMeasure mu)
      (U : Lp ℂ 2 mu ≃ₗᵢ[ℂ] H),
      (∀ᵐ z ∂mu, z.1 ≠ 0 ∧ ‖z.1‖ ^ 2 = z.1.im) ∧
      (∀ u : Lp ℂ 2 mu, ∃ h : U (mulRep mu (coordFn (resOp T)) u) ∈ T.domain,
        T.op ⟨U (mulRep mu (coordFn (resOp T)) u), h⟩
          = U (u + Complex.I • mulRep mu (coordFn (resOp T)) u)) ∧
      (∀ x ∈ T.domain, ∃ u : Lp ℂ 2 mu, x = U (mulRep mu (coordFn (resOp T)) u)) := by sorry
