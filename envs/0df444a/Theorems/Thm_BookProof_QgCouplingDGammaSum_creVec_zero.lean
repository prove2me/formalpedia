-- Prove2me | Theorems.Thm_BookProof_QgCouplingDGammaSum_creVec_zero
-- name    : BookProof.QgCouplingDGammaSum.creVec_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T05:01:51.071803+00:00
-- url     : https://prove2.me/theorems/8b53ec1c-4420-440f-9fda-c0854f7f5e30
-- title:
--   The Lean 4 theorem `creVec_zero` in the `ChapterQgCouplingDGammaSum` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.QgCouplingDGammaSum.creVec_zero` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterQgCouplingDGammaSum.lean — theorem BookProof.QgCouplingDGammaSum.creVec_zero
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib
import Definitions.Def_ChapterQgCouplingDGammaSum
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization
open BookProof.QgCouplingDGammaSum

variable {ι : Type*}



open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.YangMillsFriedrichs

noncomputable section

theorem BookProof.QgCouplingDGammaSum.creVec_zero (x : FockAlg) : creVec (0 : ℕ →₀ ℂ) x = 0 := by sorry
