-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_hFun_eq_zero
-- name    : BookProof.NavierStokesFlow.AffineFiber.hFun_eq_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T16:46:30.672983+00:00
-- url     : https://prove2.me/theorems/c6acd91a-718c-48d9-93db-b02bf0978308
-- title:
--   `BookProof.NavierStokesFlow.AffineFiber.hFun_eq_zero` (S : ShiftData ι) {X : ι → ℂ} {β : ι} (hpre : ∀ α, S.shift α = β → X α = 0) (hX : X (S.shift β) = 0) : S.hFun X β = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesAffineFiberEsa`.
--
--   `BookProof.NavierStokesFlow.AffineFiber.hFun_eq_zero` (S : ShiftData ι) {X : ι → ℂ} {β : ι} (hpre : ∀ α, S.shift α = β → X α = 0) (hX : X (S.shift β) = 0) : S.hFun X β = 0
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.AffineFiber.hFun_eq_zero`.

-- Generated from ChapterNavierStokesAffineFiberEsa.lean — theorem BookProof.NavierStokesFlow.AffineFiber.hFun_eq_zero
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

theorem BookProof.NavierStokesFlow.AffineFiber.hFun_eq_zero (S : ShiftData ι) {X : ι → ℂ} {β : ι}
    (hpre : ∀ α, S.shift α = β → X α = 0) (hX : X (S.shift β) = 0) : S.hFun X β = 0 := by sorry
