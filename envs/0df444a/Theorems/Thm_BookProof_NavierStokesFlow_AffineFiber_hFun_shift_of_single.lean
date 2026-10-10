-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_hFun_shift_of_single
-- name    : BookProof.NavierStokesFlow.AffineFiber.hFun_shift_of_single
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T16:46:31.941527+00:00
-- url     : https://prove2.me/theorems/23e55c70-0464-44ec-b34c-158c5530df7d
-- title:
--   `BookProof.NavierStokesFlow.AffineFiber.hFun_shift_of_single` (S : ShiftData ι) {X : ι → ℂ} {o : ι} (hXo : X o = 1) (hnext : X (S.shift (S.shift o)) = 0) : S.hFun X (S.shift o) = C
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesAffineFiberEsa`.
--
--   `BookProof.NavierStokesFlow.AffineFiber.hFun_shift_of_single` (S : ShiftData ι) {X : ι → ℂ} {o : ι} (hXo : X o = 1) (hnext : X (S.shift (S.shift o)) = 0) : S.hFun X (S.shift o) = Complex.I * ((S.amp o : ℝ) : ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.AffineFiber.hFun_shift_of_single`.

-- Generated from ChapterNavierStokesAffineFiberEsa.lean — theorem BookProof.NavierStokesFlow.AffineFiber.hFun_shift_of_single
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

theorem BookProof.NavierStokesFlow.AffineFiber.hFun_shift_of_single (S : ShiftData ι) {X : ι → ℂ} {o : ι}
    (hXo : X o = 1) (hnext : X (S.shift (S.shift o)) = 0) :
    S.hFun X (S.shift o) = Complex.I * ((S.amp o : ℝ) : ℂ) := by sorry
