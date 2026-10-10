-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_affH_coord_succ_succ
-- name    : BookProof.NavierStokesFlow.AffineFiber.affH_coord_succ_succ
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T16:49:01.577978+00:00
-- url     : https://prove2.me/theorems/13ceb161-6561-471d-b141-3b2316900261
-- title:
--   `BookProof.NavierStokesFlow.AffineFiber.affH_coord_succ_succ` {κ c : ℝ} (hκ : 0 ≤ κ) (hc : 0 ≤ c) (n : ℕ) : ((affH hκ hc (basisState κ c n) : L2I ℕ) : ℕ → ℂ) (n + 2) = Complex.I *
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesAffineFiberEsa`.
--
--   `BookProof.NavierStokesFlow.AffineFiber.affH_coord_succ_succ` {κ c : ℝ} (hκ : 0 ≤ κ) (hc : 0 ≤ c) (n : ℕ) : ((affH hκ hc (basisState κ c n) : L2I ℕ) : ℕ → ℂ) (n + 2) = Complex.I * ((amp κ n : ℝ) : ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.AffineFiber.affH_coord_succ_succ`.

-- Generated from ChapterNavierStokesAffineFiberEsa.lean — theorem BookProof.NavierStokesFlow.AffineFiber.affH_coord_succ_succ
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

theorem BookProof.NavierStokesFlow.AffineFiber.affH_coord_succ_succ {κ c : ℝ} (hκ : 0 ≤ κ) (hc : 0 ≤ c) (n : ℕ) :
    ((affH hκ hc (basisState κ c n) : L2I ℕ) : ℕ → ℂ) (n + 2)
      = Complex.I * ((amp κ n : ℝ) : ℂ) := by sorry
