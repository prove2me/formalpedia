-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_affH_symmetricOn
-- name    : BookProof.NavierStokesFlow.AffineFiber.affH_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T16:48:02.059988+00:00
-- url     : https://prove2.me/theorems/a45c03bb-2e4e-4743-951e-8c7a89bd55c4
-- title:
--   `BookProof.NavierStokesFlow.AffineFiber.affH_symmetricOn` {κ c : ℝ} (hκ : 0 ≤ κ) (hc : 0 ≤ c) : SymmetricOn (maxDom (oscSymbol (affMu κ c))) (affH hκ hc)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesAffineFiberEsa`.
--
--   `BookProof.NavierStokesFlow.AffineFiber.affH_symmetricOn` {κ c : ℝ} (hκ : 0 ≤ κ) (hc : 0 ≤ c) : SymmetricOn (maxDom (oscSymbol (affMu κ c))) (affH hκ hc)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.AffineFiber.affH_symmetricOn`.

-- Generated from ChapterNavierStokesAffineFiberEsa.lean — theorem BookProof.NavierStokesFlow.AffineFiber.affH_symmetricOn
import Mathlib
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterFarisLavineCore
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

theorem BookProof.NavierStokesFlow.AffineFiber.affH_symmetricOn {κ c : ℝ} (hκ : 0 ≤ κ) (hc : 0 ≤ c) :
    SymmetricOn (maxDom (oscSymbol (affMu κ c))) (affH hκ hc) := by sorry
