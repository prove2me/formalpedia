-- Prove2me | Theorems.Thm_BookProof_OperatorSeries_commForm_add
-- name    : BookProof.OperatorSeries.commForm_add
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T21:21:28.870373+00:00
-- url     : https://prove2.me/theorems/8f9019ba-4cd9-4c84-8c8a-1cdeaa086c7b
-- title:
--   `BookProof.OperatorSeries.commForm_add` (H₁ H₂ N : D →ₗ[ℂ] F) (x : D) : commForm (H₁ + H₂) N x = commForm H₁ N x + commForm H₂ N x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterOperatorSeriesEsa`.
--
--   `BookProof.OperatorSeries.commForm_add` (H₁ H₂ N : D →ₗ[ℂ] F) (x : D) : commForm (H₁ + H₂) N x = commForm H₁ N x + commForm H₂ N x
--
--   Formalization note: Lean 4 identifier `BookProof.OperatorSeries.commForm_add`.

-- Generated from ChapterOperatorSeriesEsa.lean — theorem BookProof.OperatorSeries.commForm_add
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

theorem BookProof.OperatorSeries.commForm_add (H₁ H₂ N : D →ₗ[ℂ] F) (x : D) :
    commForm (H₁ + H₂) N x = commForm H₁ N x + commForm H₂ N x := by sorry
