-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_affH_essentiallySelfAdjointOn_core
-- name    : BookProof.NavierStokesFlow.AffineFiber.affH_essentiallySelfAdjointOn_core
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T16:48:13.735406+00:00
-- url     : https://prove2.me/theorems/f2af85ce-497c-41ba-b6a1-792fb95145e8
-- title:
--   `BookProof.NavierStokesFlow.AffineFiber.affH_essentiallySelfAdjointOn_core` {κ c : ℝ} (hκ : 0 ≤ κ) (hc : 0 ≤ c) : EssentiallySelfAdjointOn (lpFiniteModes ℕ) ((affH hκ hc).comp (Sub
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesAffineFiberEsa`.
--
--   `BookProof.NavierStokesFlow.AffineFiber.affH_essentiallySelfAdjointOn_core` {κ c : ℝ} (hκ : 0 ≤ κ) (hc : 0 ≤ c) : EssentiallySelfAdjointOn (lpFiniteModes ℕ) ((affH hκ hc).comp (Submodule.inclusion (finiteModes_le_maxDom (oscSymbol (affMu κ c)))))
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.AffineFiber.affH_essentiallySelfAdjointOn_core`.

-- Generated from ChapterNavierStokesAffineFiberEsa.lean — theorem BookProof.NavierStokesFlow.AffineFiber.affH_essentiallySelfAdjointOn_core
import Mathlib
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.AffineFiber


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian

variable {ι : Type*}

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable (P : PairShift ι)

theorem BookProof.NavierStokesFlow.AffineFiber.affH_essentiallySelfAdjointOn_core {κ c : ℝ} (hκ : 0 ≤ κ) (hc : 0 ≤ c) :
    EssentiallySelfAdjointOn (lpFiniteModes ℕ)
      ((affH hκ hc).comp
        (Submodule.inclusion (finiteModes_le_maxDom (oscSymbol (affMu κ c))))) := by sorry
