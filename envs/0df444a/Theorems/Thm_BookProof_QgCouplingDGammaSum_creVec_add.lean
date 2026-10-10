-- Prove2me | Theorems.Thm_BookProof_QgCouplingDGammaSum_creVec_add
-- name    : BookProof.QgCouplingDGammaSum.creVec_add
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:16:40.261977+00:00
-- url     : https://prove2.me/theorems/16ebda68-e9dd-48e8-b4c2-bcb77b450692
-- title:
--   `BookProof.QgCouplingDGammaSum.creVec_add` (v w : ℕ →₀ ℂ) (x : FockAlg) : creVec (v + w) x = creVec v x + creVec w x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgCouplingDGammaSum`.
--
--   `BookProof.QgCouplingDGammaSum.creVec_add` (v w : ℕ →₀ ℂ) (x : FockAlg) : creVec (v + w) x = creVec v x + creVec w x
--
--   Formalization note: Lean 4 identifier `BookProof.QgCouplingDGammaSum.creVec_add`.

-- Generated from ChapterQgCouplingDGammaSum.lean — theorem BookProof.QgCouplingDGammaSum.creVec_add
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



open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.YangMillsFriedrichs

noncomputable section

variable {ι : Type*}

theorem BookProof.QgCouplingDGammaSum.creVec_add (v w : ℕ →₀ ℂ) (x : FockAlg) :
    creVec (v + w) x = creVec v x + creVec w x := by sorry
