-- Prove2me | Theorems.Thm_BookProof_UnboundedSpectralModel_unbounded_multiplication_model_general_inc
-- name    : BookProof.UnboundedSpectralModel.unbounded_multiplication_model_general_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T14:00:35.651412+00:00
-- url     : https://prove2.me/theorems/85cdf071-ba7d-4140-bc29-a5f5a6d41775
-- title:
--   `BookProof.UnboundedSpectralModel.unbounded_multiplication_model_general_inc` (T : UnboundedSelfAdjoint H) : ∃ (S : Set H) (mu : S → Measure (spectrum ℂ (resOp T))) (V : ∀ x : S, Lp ℂ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterUnboundedSpectralModel`.
--
--   `BookProof.UnboundedSpectralModel.unbounded_multiplication_model_general_inc` (T : UnboundedSelfAdjoint H) : ∃ (S : Set H) (mu : S → Measure (spectrum ℂ (resOp T))) (V : ∀ x : S, Lp ℂ 2 (mu x) →ₗᵢ[ℂ] H), (∀ x : S, IsProbabilityMeasure (mu x)) ∧ IsHilbertSum ℂ (fun x : S => Lp ℂ 2 (mu x)) V ∧ (∀ x : S, ∀ᵐ z ∂(mu x), z.1 ≠ 0 ∧ ‖z.1‖ ^ 2 = z.1.im) ∧ (∀ (x : S) (u : Lp ℂ 2 (mu x)), ∃ h : V x (mulRep (mu x) (coordFn (resOp T)) u) ∈ T.domain, T.op ⟨V x (mulRep (mu x) (coordFn (resOp T)) u), h⟩ = V x (u + Complex.I • mulRep (mu x) (coordFn (resOp T)) u))
--
--   Formalization note: Lean 4 identifier `BookProof.UnboundedSpectralModel.unbounded_multiplication_model_general_inc`.
--
--   Replaces the unuploadable node `BookProof_UnboundedSpectralModel_unbounded_multiplication_model_general`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.

-- Generated from ChapterUnboundedSpectralModel.lean — theorem BookProof.UnboundedSpectralModel.unbounded_multiplication_model_general_inc
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

theorem BookProof.UnboundedSpectralModel.unbounded_multiplication_model_general_inc (T : UnboundedSelfAdjoint H) :
    ∃ (S : Set H) (mu : S → Measure (spectrum ℂ (resOp T)))
      (V : ∀ x : S, Lp ℂ 2 (mu x) →ₗᵢ[ℂ] H),
      (∀ x : S, IsProbabilityMeasure (mu x)) ∧
      IsHilbertSum ℂ (fun x : S => Lp ℂ 2 (mu x)) V ∧
      (∀ x : S, ∀ᵐ z ∂(mu x), z.1 ≠ 0 ∧ ‖z.1‖ ^ 2 = z.1.im) ∧
      (∀ (x : S) (u : Lp ℂ 2 (mu x)),
        ∃ h : V x (mulRep (mu x) (coordFn (resOp T)) u) ∈ T.domain,
          T.op ⟨V x (mulRep (mu x) (coordFn (resOp T)) u), h⟩
            = V x (u + Complex.I • mulRep (mu x) (coordFn (resOp T)) u)) := by sorry
