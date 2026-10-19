-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_MomentumPerturbation_commForm_witness_eq_neg_two
-- name    : BookProof.NavierStokesFlow.MomentumPerturbation.commForm_witness_eq_neg_two
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:22:36.6749+00:00
-- url     : https://prove2.me/theorems/0ef7ac4a-cd1e-4f51-a6f6-53ed12e0f6b2
-- title:
--   `BookProof.NavierStokesFlow.MomentumPerturbation.commForm_witness_eq_neg_two` : commForm (pertHam linSymbol (eState 0) (eState 1)) (diagMax linSymbol) ⟨testState, testState_mem_max
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesMomentumPerturbation`.
--
--   `BookProof.NavierStokesFlow.MomentumPerturbation.commForm_witness_eq_neg_two` : commForm (pertHam linSymbol (eState 0) (eState 1)) (diagMax linSymbol) ⟨testState, testState_mem_maxDom⟩ = -2
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.MomentumPerturbation.commForm_witness_eq_neg_two`.

-- Generated from ChapterNavierStokesMomentumPerturbation.lean — theorem BookProof.NavierStokesFlow.MomentumPerturbation.commForm_witness_eq_neg_two
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumPerturbation
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesFockManyMode
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Theorems.Thm_BookProof_NavierStokesFlow_MomentumPerturbation_testState_mem_maxDom
open BookProof.NavierStokesFlow.FockManyMode
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumPerturbation




open LpNat BookProof.FarisLavine IkebeKato

variable {ι : Type*}

theorem BookProof.NavierStokesFlow.MomentumPerturbation.commForm_witness_eq_neg_two :
    commForm (pertHam linSymbol (eState 0) (eState 1)) (diagMax linSymbol)
      ⟨testState, testState_mem_maxDom⟩ = -2 := by sorry
