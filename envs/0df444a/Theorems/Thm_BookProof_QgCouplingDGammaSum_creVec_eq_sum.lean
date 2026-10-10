-- Prove2me | Theorems.Thm_BookProof_QgCouplingDGammaSum_creVec_eq_sum
-- name    : BookProof.QgCouplingDGammaSum.creVec_eq_sum
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:16:25.87398+00:00
-- url     : https://prove2.me/theorems/ca3daeac-5933-49a5-8335-4b33117d6ea0
-- title:
--   `BookProof.QgCouplingDGammaSum.creVec_eq_sum` {v : ℕ →₀ ℂ} {L : Finset ℕ} (hL : v.support ⊆ L) (x : FockAlg) : creVec v x = ∑ j ∈ L, v j • creA j x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgCouplingDGammaSum`.
--
--   `BookProof.QgCouplingDGammaSum.creVec_eq_sum` {v : ℕ →₀ ℂ} {L : Finset ℕ} (hL : v.support ⊆ L) (x : FockAlg) : creVec v x = ∑ j ∈ L, v j • creA j x
--
--   Formalization note: Lean 4 identifier `BookProof.QgCouplingDGammaSum.creVec_eq_sum`.

-- Generated from ChapterQgCouplingDGammaSum.lean — theorem BookProof.QgCouplingDGammaSum.creVec_eq_sum
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

theorem BookProof.QgCouplingDGammaSum.creVec_eq_sum {v : ℕ →₀ ℂ} {L : Finset ℕ} (hL : v.support ⊆ L) (x : FockAlg) :
    creVec v x = ∑ j ∈ L, v j • creA j x := by sorry
