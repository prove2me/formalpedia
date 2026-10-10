-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_affH_not_bounded
-- name    : BookProof.NavierStokesFlow.AffineFiber.affH_not_bounded
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T16:49:56.679298+00:00
-- url     : https://prove2.me/theorems/a6c822a8-1575-4fab-a4a6-3787a1a1d711
-- title:
--   `BookProof.NavierStokesFlow.AffineFiber.affH_not_bounded` {κ c : ℝ} (hκ : 0 < κ) (hc : 0 ≤ c) (C : ℝ) : ∃ n : ℕ, ‖(basisState κ c n : L2I ℕ)‖ = 1 ∧ C < ‖(affH hκ.le hc...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesAffineFiberEsa`.
--
--   `BookProof.NavierStokesFlow.AffineFiber.affH_not_bounded` {κ c : ℝ} (hκ : 0 < κ) (hc : 0 ≤ c) (C : ℝ) : ∃ n : ℕ, ‖(basisState κ c n : L2I ℕ)‖ = 1 ∧ C < ‖(affH hκ.le hc (basisState κ c n) : L2I ℕ)‖
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.AffineFiber.affH_not_bounded`.

-- Generated from ChapterNavierStokesAffineFiberEsa.lean — theorem BookProof.NavierStokesFlow.AffineFiber.affH_not_bounded
import Mathlib
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
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

theorem BookProof.NavierStokesFlow.AffineFiber.affH_not_bounded {κ c : ℝ} (hκ : 0 < κ) (hc : 0 ≤ c) (C : ℝ) :
    ∃ n : ℕ, ‖(basisState κ c n : L2I ℕ)‖ = 1
      ∧ C < ‖(affH hκ.le hc (basisState κ c n) : L2I ℕ)‖ := by sorry
