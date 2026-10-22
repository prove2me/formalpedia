-- Prove2me | Theorems.Thm_BookProof_UnboundedSpectralModel_cayley_pointwise_inc
-- name    : BookProof.UnboundedSpectralModel.cayley_pointwise_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T13:59:49.069994+00:00
-- url     : https://prove2.me/theorems/f9482e7b-e2eb-4716-adff-a1d2afc79673
-- title:
--   `BookProof.UnboundedSpectralModel.cayley_pointwise_inc` (w : ℂ) : w - (starRingEnd ℂ) w - (2 * Complex.I) * ((starRingEnd ℂ) w * w) = (2 * Complex.I) * (((w.im - ‖w‖ ^ 2 : ℝ) : ℂ))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterUnboundedSpectralModel`.
--
--   `BookProof.UnboundedSpectralModel.cayley_pointwise_inc` (w : ℂ) : w - (starRingEnd ℂ) w - (2 * Complex.I) * ((starRingEnd ℂ) w * w) = (2 * Complex.I) * (((w.im - ‖w‖ ^ 2 : ℝ) : ℂ))
--
--   Formalization note: Lean 4 identifier `BookProof.UnboundedSpectralModel.cayley_pointwise_inc`.
--
--   Replaces the unuploadable node `BookProof_UnboundedSpectralModel_cayley_pointwise`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.

-- Generated from ChapterUnboundedSpectralModel.lean — theorem BookProof.UnboundedSpectralModel.cayley_pointwise_inc
import Definitions.Def_ChapterUnitaryTransport
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterSpectralMultiplication
import Definitions.Def_ChapterSpectralDirectSum
import Mathlib
import Definitions.Def_ChapterUnboundedSpectralModel
open BookProof.UnboundedSpectralModel


noncomputable section

open MeasureTheory Complex
open scoped InnerProductSpace


open BookProof.ChapterUnitaryTransport BookProof.ChapterStoneResolvent
open BookProof.ChapterAbelianGelfandModel BookProof.ChapterSpectralMultiplication
open BookProof.ChapterSpectralDirectSum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem BookProof.UnboundedSpectralModel.cayley_pointwise_inc (w : ℂ) :
    w - (starRingEnd ℂ) w - (2 * Complex.I) * ((starRingEnd ℂ) w * w)
      = (2 * Complex.I) * (((w.im - ‖w‖ ^ 2 : ℝ) : ℂ)) := by sorry
