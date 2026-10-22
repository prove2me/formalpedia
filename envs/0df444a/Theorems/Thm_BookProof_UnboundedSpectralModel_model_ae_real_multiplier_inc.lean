-- Prove2me | Theorems.Thm_BookProof_UnboundedSpectralModel_model_ae_real_multiplier_inc
-- name    : BookProof.UnboundedSpectralModel.model_ae_real_multiplier_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T13:59:57.259641+00:00
-- url     : https://prove2.me/theorems/4df29946-5a1b-4f1c-a83a-18321d497869
-- title:
--   `BookProof.UnboundedSpectralModel.model_ae_real_multiplier_inc` [IsFiniteMeasure mu] : ∀ᵐ z ∂mu, 1 + Complex.I * z.1 = ((z.1.re / ‖z.1‖ ^ 2 : ℝ) : ℂ) * z.1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterUnboundedSpectralModel`.
--
--   `BookProof.UnboundedSpectralModel.model_ae_real_multiplier_inc` [IsFiniteMeasure mu] : ∀ᵐ z ∂mu, 1 + Complex.I * z.1 = ((z.1.re / ‖z.1‖ ^ 2 : ℝ) : ℂ) * z.1
--
--   Formalization note: Lean 4 identifier `BookProof.UnboundedSpectralModel.model_ae_real_multiplier_inc`.
--
--   Replaces the unuploadable node `BookProof_UnboundedSpectralModel_model_ae_real_multiplier`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.

-- Generated from ChapterUnboundedSpectralModel.lean — theorem BookProof.UnboundedSpectralModel.model_ae_real_multiplier_inc
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

theorem BookProof.UnboundedSpectralModel.model_ae_real_multiplier_inc [IsFiniteMeasure mu] :
    ∀ᵐ z ∂mu, 1 + Complex.I * z.1 = ((z.1.re / ‖z.1‖ ^ 2 : ℝ) : ℂ) * z.1 := by sorry
