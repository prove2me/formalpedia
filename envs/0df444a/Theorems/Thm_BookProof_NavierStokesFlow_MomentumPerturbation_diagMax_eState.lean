-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_MomentumPerturbation_diagMax_eState
-- name    : BookProof.NavierStokesFlow.MomentumPerturbation.diagMax_eState
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:42:06.723742+00:00
-- url     : https://prove2.me/theorems/144aa95f-3d8a-48b1-b701-82fd5cf6a059
-- title:
--   `BookProof.NavierStokesFlow.MomentumPerturbation.diagMax_eState` (k : ℕ) : (diagMax linSymbol ⟨eState k, eState_mem_maxDom k⟩ : L2I ℕ) = ((linSymbol k : ℂ)) • eState k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesMomentumPerturbation`.
--
--   `BookProof.NavierStokesFlow.MomentumPerturbation.diagMax_eState` (k : ℕ) : (diagMax linSymbol ⟨eState k, eState_mem_maxDom k⟩ : L2I ℕ) = ((linSymbol k : ℂ)) • eState k
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.MomentumPerturbation.diagMax_eState`.

-- Generated from ChapterNavierStokesMomentumPerturbation.lean — theorem BookProof.NavierStokesFlow.MomentumPerturbation.diagMax_eState
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumPerturbation
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Theorems.Thm_BookProof_NavierStokesFlow_MomentumPerturbation_eState_mem_maxDom
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumPerturbation




open LpNat BookProof.FarisLavine IkebeKato

variable {ι : Type*}

theorem BookProof.NavierStokesFlow.MomentumPerturbation.diagMax_eState (k : ℕ) :
    (diagMax linSymbol ⟨eState k, eState_mem_maxDom k⟩ : L2I ℕ)
      = ((linSymbol k : ℂ)) • eState k := by sorry
