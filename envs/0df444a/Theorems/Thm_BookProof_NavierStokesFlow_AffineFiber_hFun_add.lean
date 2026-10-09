-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_hFun_add
-- name    : BookProof.NavierStokesFlow.AffineFiber.hFun_add
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T09:32:39.863965+00:00
-- url     : https://prove2.me/theorems/12189ec1-f928-4a95-8a15-9502d3441dd1
-- title:
--   `BookProof.NavierStokesFlow.AffineFiber.hFun_add` (S : ShiftData ι) (X Y : ι → ℂ) (β : ι) : S.hFun (fun α => X α + Y α) β = S.hFun X β + S.hFun Y β
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesAffineFiberEsa`.
--
--   `BookProof.NavierStokesFlow.AffineFiber.hFun_add` (S : ShiftData ι) (X Y : ι → ℂ) (β : ι) : S.hFun (fun α => X α + Y α) β = S.hFun X β + S.hFun Y β
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.AffineFiber.hFun_add`.

-- Generated from ChapterNavierStokesAffineFiberEsa.lean — theorem BookProof.NavierStokesFlow.AffineFiber.hFun_add
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

theorem BookProof.NavierStokesFlow.AffineFiber.hFun_add (S : ShiftData ι) (X Y : ι → ℂ) (β : ι) :
    S.hFun (fun α => X α + Y α) β = S.hFun X β + S.hFun Y β := by sorry
