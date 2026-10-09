-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_hFun_smul
-- name    : BookProof.NavierStokesFlow.AffineFiber.hFun_smul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T10:18:48.628361+00:00
-- url     : https://prove2.me/theorems/11d8d45e-039a-471f-87f1-878fbb5d67b9
-- title:
--   `BookProof.NavierStokesFlow.AffineFiber.hFun_smul` (S : ShiftData ι) (a : ℂ) (X : ι → ℂ) (β : ι) : S.hFun (fun α => a * X α) β = a * S.hFun X β
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesAffineFiberEsa`.
--
--   `BookProof.NavierStokesFlow.AffineFiber.hFun_smul` (S : ShiftData ι) (a : ℂ) (X : ι → ℂ) (β : ι) : S.hFun (fun α => a * X α) β = a * S.hFun X β
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.AffineFiber.hFun_smul`.

-- Generated from ChapterNavierStokesAffineFiberEsa.lean — theorem BookProof.NavierStokesFlow.AffineFiber.hFun_smul
import Mathlib
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesShiftHamiltonian
import Definitions.Def_ChapterStoneResolvent
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ShiftHamiltonian
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.AffineFiber


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian

variable {ι : Type*}

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
open ShiftHamiltonian

theorem BookProof.NavierStokesFlow.AffineFiber.hFun_smul (S : ShiftData ι) (a : ℂ) (X : ι → ℂ) (β : ι) :
    S.hFun (fun α => a * X α) β = a * S.hFun X β := by sorry
