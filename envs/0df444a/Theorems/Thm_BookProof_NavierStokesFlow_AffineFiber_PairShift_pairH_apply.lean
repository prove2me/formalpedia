-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_PairShift_pairH_apply
-- name    : BookProof.NavierStokesFlow.AffineFiber.PairShift.pairH_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T16:46:47.011558+00:00
-- url     : https://prove2.me/theorems/825cb332-c1ea-45ed-aa4f-828d41707ff7
-- title:
--   `BookProof.NavierStokesFlow.AffineFiber.PairShift.pairH_apply` (x : maxDom P.sym) : (pairH P x : L2I ι) = (ShiftData.shiftH P.fst x : L2I ι) + (ShiftData.shiftH P.snd x : L2I ι)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesAffineFiberEsa`.
--
--   `BookProof.NavierStokesFlow.AffineFiber.PairShift.pairH_apply` (x : maxDom P.sym) : (pairH P x : L2I ι) = (ShiftData.shiftH P.fst x : L2I ι) + (ShiftData.shiftH P.snd x : L2I ι)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.AffineFiber.PairShift.pairH_apply`.

-- Generated from ChapterNavierStokesAffineFiberEsa.lean — theorem BookProof.NavierStokesFlow.AffineFiber.PairShift.pairH_apply
import Mathlib
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesShiftHamiltonian
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.AffineFiber


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian

variable {ι : Type*}

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable (P : PairShift ι)

theorem BookProof.NavierStokesFlow.AffineFiber.PairShift.pairH_apply (x : maxDom P.sym) :
    (pairH P x : L2I ι) = (ShiftData.shiftH P.fst x : L2I ι)
      + (ShiftData.shiftH P.snd x : L2I ι) := by sorry
