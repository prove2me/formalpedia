-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_PairShift_pairH_symmetricOn
-- name    : BookProof.NavierStokesFlow.AffineFiber.PairShift.pairH_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T16:47:18.288754+00:00
-- url     : https://prove2.me/theorems/684dce00-9c54-4465-bf32-8ffb81b4e022
-- title:
--   `BookProof.NavierStokesFlow.AffineFiber.PairShift.pairH_symmetricOn` : SymmetricOn (maxDom P.sym) (pairH P)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesAffineFiberEsa`.
--
--   `BookProof.NavierStokesFlow.AffineFiber.PairShift.pairH_symmetricOn` : SymmetricOn (maxDom P.sym) (pairH P)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.AffineFiber.PairShift.pairH_symmetricOn`.

-- Generated from ChapterNavierStokesAffineFiberEsa.lean — theorem BookProof.NavierStokesFlow.AffineFiber.PairShift.pairH_symmetricOn
import Mathlib
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterFarisLavineCore
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

theorem BookProof.NavierStokesFlow.AffineFiber.PairShift.pairH_symmetricOn : SymmetricOn (maxDom P.sym) (pairH P) := by sorry
