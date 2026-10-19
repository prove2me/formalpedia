-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_nsCauchy_existsUnique
-- name    : BookProof.NavierStokesFlow.nsCauchy_existsUnique
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:16:37.184953+00:00
-- url     : https://prove2.me/theorems/4a17c961-b7cc-4765-a06a-b45b0ef9f362
-- title:
--   `BookProof.NavierStokesFlow.nsCauchy_existsUnique` (psi : Fin n → ℂ) : ∃! y : ℝ → Fin n → ℂ, y 0 = psi ∧ ∀ t, HasDerivAt y ((Complex.I • nsHamiltonian d) *ᵥ y t) t
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesCauchy`.
--
--   `BookProof.NavierStokesFlow.nsCauchy_existsUnique` (psi : Fin n → ℂ) : ∃! y : ℝ → Fin n → ℂ, y 0 = psi ∧ ∀ t, HasDerivAt y ((Complex.I • nsHamiltonian d) *ᵥ y t) t
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.nsCauchy_existsUnique`.

-- Generated from ChapterNavierStokesCauchy.lean — theorem BookProof.NavierStokesFlow.nsCauchy_existsUnique
import Mathlib
import Definitions.Def_ChapterNavierStokesCauchy
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow


open scoped BigOperators Matrix Matrix.Norms.Operator

variable {n : ℕ}
variable {n : ℕ} (d : NSTruncation n)

theorem BookProof.NavierStokesFlow.nsCauchy_existsUnique (psi : Fin n → ℂ) :
    ∃! y : ℝ → Fin n → ℂ,
      y 0 = psi ∧ ∀ t, HasDerivAt y ((Complex.I • nsHamiltonian d) *ᵥ y t) t := by sorry
