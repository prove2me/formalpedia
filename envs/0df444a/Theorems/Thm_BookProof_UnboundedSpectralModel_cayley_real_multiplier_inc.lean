-- Prove2me | Theorems.Thm_BookProof_UnboundedSpectralModel_cayley_real_multiplier_inc
-- name    : BookProof.UnboundedSpectralModel.cayley_real_multiplier_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T13:59:48.404048+00:00
-- url     : https://prove2.me/theorems/17e62359-2346-48b6-8650-cf14eda7d82a
-- title:
--   `BookProof.UnboundedSpectralModel.cayley_real_multiplier_inc` {w : ℂ} (h : ‖w‖ ^ 2 = w.im) (hw : w ≠ 0) : 1 + Complex.I * w = ((w.re / ‖w‖ ^ 2 : ℝ) : ℂ) * w
-- statement:
--   Prove the following Lean 4 theorem from `ChapterUnboundedSpectralModel`.
--
--   `BookProof.UnboundedSpectralModel.cayley_real_multiplier_inc` {w : ℂ} (h : ‖w‖ ^ 2 = w.im) (hw : w ≠ 0) : 1 + Complex.I * w = ((w.re / ‖w‖ ^ 2 : ℝ) : ℂ) * w
--
--   Formalization note: Lean 4 identifier `BookProof.UnboundedSpectralModel.cayley_real_multiplier_inc`.
--
--   Replaces the unuploadable node `BookProof_UnboundedSpectralModel_cayley_real_multiplier`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.

-- Generated from ChapterUnboundedSpectralModel.lean — theorem BookProof.UnboundedSpectralModel.cayley_real_multiplier_inc
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

theorem BookProof.UnboundedSpectralModel.cayley_real_multiplier_inc {w : ℂ} (h : ‖w‖ ^ 2 = w.im) (hw : w ≠ 0) :
    1 + Complex.I * w = ((w.re / ‖w‖ ^ 2 : ℝ) : ℂ) * w := by sorry
