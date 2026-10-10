-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_support_hFun
-- name    : BookProof.NavierStokesFlow.AffineFiber.support_hFun
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T10:18:47.380449+00:00
-- url     : https://prove2.me/theorems/11e73d09-6f77-4f96-8231-b18209d80595
-- title:
--   `BookProof.NavierStokesFlow.AffineFiber.support_hFun` (S : ShiftData ι) (X : ι → ℂ) : Function.support (S.hFun X) ⊆ S.shift '' Function.support X ∪ S.shift ⁻¹' Function.support X
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesAffineFiberEsa`.
--
--   `BookProof.NavierStokesFlow.AffineFiber.support_hFun` (S : ShiftData ι) (X : ι → ℂ) : Function.support (S.hFun X) ⊆ S.shift '' Function.support X ∪ S.shift ⁻¹' Function.support X
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.AffineFiber.support_hFun`.

-- Generated from ChapterNavierStokesAffineFiberEsa.lean — theorem BookProof.NavierStokesFlow.AffineFiber.support_hFun
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

theorem BookProof.NavierStokesFlow.AffineFiber.support_hFun (S : ShiftData ι) (X : ι → ℂ) :
    Function.support (S.hFun X)
      ⊆ S.shift '' Function.support X ∪ S.shift ⁻¹' Function.support X := by sorry
