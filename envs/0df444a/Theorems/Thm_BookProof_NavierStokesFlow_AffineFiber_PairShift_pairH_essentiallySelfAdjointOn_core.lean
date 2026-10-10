-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_PairShift_pairH_essentiallySelfAdjointOn_core
-- name    : BookProof.NavierStokesFlow.AffineFiber.PairShift.pairH_essentiallySelfAdjointOn_core
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T16:47:54.229099+00:00
-- url     : https://prove2.me/theorems/32b9e3bd-af5e-4211-95b0-ebe49b4b0704
-- title:
--   `BookProof.NavierStokesFlow.AffineFiber.PairShift.pairH_essentiallySelfAdjointOn_core` : EssentiallySelfAdjointOn (lpFiniteModes ι) ((pairH P).comp (Submodule.inclusion (finiteMode
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesAffineFiberEsa`.
--
--   `BookProof.NavierStokesFlow.AffineFiber.PairShift.pairH_essentiallySelfAdjointOn_core` : EssentiallySelfAdjointOn (lpFiniteModes ι) ((pairH P).comp (Submodule.inclusion (finiteModes_le_maxDom P.sym)))
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.AffineFiber.PairShift.pairH_essentiallySelfAdjointOn_core`.

-- Generated from ChapterNavierStokesAffineFiberEsa.lean — theorem BookProof.NavierStokesFlow.AffineFiber.PairShift.pairH_essentiallySelfAdjointOn_core
import Mathlib
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.AffineFiber


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian

variable {ι : Type*}

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable (P : PairShift ι)

theorem BookProof.NavierStokesFlow.AffineFiber.PairShift.pairH_essentiallySelfAdjointOn_core :
    EssentiallySelfAdjointOn (lpFiniteModes ι)
      ((pairH P).comp (Submodule.inclusion (finiteModes_le_maxDom P.sym))) := by sorry
