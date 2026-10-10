-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_PairShift_pairH_coe
-- name    : BookProof.NavierStokesFlow.AffineFiber.PairShift.pairH_coe
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T16:47:08.817564+00:00
-- url     : https://prove2.me/theorems/7f1a6fdf-0a1b-4138-8dd0-6196bfd5b91c
-- title:
--   `BookProof.NavierStokesFlow.AffineFiber.PairShift.pairH_coe` (x : maxDom P.sym) (β : ι) : ((pairH P x : L2I ι) : ι → ℂ) β = P.fst.hFun ((x : L2I ι) : ι → ℂ) β + P.snd.hFun ((x : L2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesAffineFiberEsa`.
--
--   `BookProof.NavierStokesFlow.AffineFiber.PairShift.pairH_coe` (x : maxDom P.sym) (β : ι) : ((pairH P x : L2I ι) : ι → ℂ) β = P.fst.hFun ((x : L2I ι) : ι → ℂ) β + P.snd.hFun ((x : L2I ι) : ι → ℂ) β
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.AffineFiber.PairShift.pairH_coe`.

-- Generated from ChapterNavierStokesAffineFiberEsa.lean — theorem BookProof.NavierStokesFlow.AffineFiber.PairShift.pairH_coe
import Mathlib
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesShiftHamiltonian
open BookProof.NavierStokesFlow
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

theorem BookProof.NavierStokesFlow.AffineFiber.PairShift.pairH_coe (x : maxDom P.sym) (β : ι) :
    ((pairH P x : L2I ι) : ι → ℂ) β
      = P.fst.hFun ((x : L2I ι) : ι → ℂ) β + P.snd.hFun ((x : L2I ι) : ι → ℂ) β := by sorry
