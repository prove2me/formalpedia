-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_affH_coord_succ
-- name    : BookProof.NavierStokesFlow.AffineFiber.affH_coord_succ
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T16:49:07.806233+00:00
-- url     : https://prove2.me/theorems/8f73cd51-e4db-439f-90ca-671de6c84c37
-- title:
--   `BookProof.NavierStokesFlow.AffineFiber.affH_coord_succ` {κ c : ℝ} (hκ : 0 ≤ κ) (hc : 0 ≤ c) (n : ℕ) : ((affH hκ hc (basisState κ c n) : L2I ℕ) : ℕ → ℂ) (n + 1) = Complex.I *...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesAffineFiberEsa`.
--
--   `BookProof.NavierStokesFlow.AffineFiber.affH_coord_succ` {κ c : ℝ} (hκ : 0 ≤ κ) (hc : 0 ≤ c) (n : ℕ) : ((affH hκ hc (basisState κ c n) : L2I ℕ) : ℕ → ℂ) (n + 1) = Complex.I * ((shear c n : ℝ) : ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.AffineFiber.affH_coord_succ`.

-- Generated from ChapterNavierStokesAffineFiberEsa.lean — theorem BookProof.NavierStokesFlow.AffineFiber.affH_coord_succ
import Mathlib
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterStoneResolvent
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.AffineFiber


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian

variable {ι : Type*}

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable (P : PairShift ι)

theorem BookProof.NavierStokesFlow.AffineFiber.affH_coord_succ {κ c : ℝ} (hκ : 0 ≤ κ) (hc : 0 ≤ c) (n : ℕ) :
    ((affH hκ hc (basisState κ c n) : L2I ℕ) : ℕ → ℂ) (n + 1)
      = Complex.I * ((shear c n : ℝ) : ℂ) := by sorry
