-- Prove2me | Theorems.Thm_BookProof_OperatorSeries_commForm_eq_neg_two_im
-- name    : BookProof.OperatorSeries.commForm_eq_neg_two_im
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T21:20:55.523514+00:00
-- url     : https://prove2.me/theorems/f5873356-a094-40e0-b006-5592bdaa8030
-- title:
--   `BookProof.OperatorSeries.commForm_eq_neg_two_im` (H N : D →ₗ[ℂ] F) (x : D) : commForm H N x = -2 * (inner ℂ (H x) (N x) : ℂ).im
-- statement:
--   Prove the following Lean 4 theorem from `ChapterOperatorSeriesEsa`.
--
--   `BookProof.OperatorSeries.commForm_eq_neg_two_im` (H N : D →ₗ[ℂ] F) (x : D) : commForm H N x = -2 * (inner ℂ (H x) (N x) : ℂ).im
--
--   Formalization note: Lean 4 identifier `BookProof.OperatorSeries.commForm_eq_neg_two_im`.

-- Generated from ChapterOperatorSeriesEsa.lean — theorem BookProof.OperatorSeries.commForm_eq_neg_two_im
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesDeficiency
import Mathlib
import Definitions.Def_ChapterOperatorSeriesEsa
import Definitions.Def_ChapterFarisLavineCore
open BookProof.OperatorSeries

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}



open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.LpNat

noncomputable section

theorem BookProof.OperatorSeries.commForm_eq_neg_two_im (H N : D →ₗ[ℂ] F) (x : D) :
    commForm H N x = -2 * (inner ℂ (H x) (N x) : ℂ).im := by sorry
