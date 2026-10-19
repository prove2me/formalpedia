-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianNS_cauchy_existsUnique
-- name    : BookProof.NavierStokesFlow.LagrangianNS.cauchy_existsUnique
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:17:00.833218+00:00
-- url     : https://prove2.me/theorems/267b0497-f14c-49bd-a209-399ad22c272d
-- title:
--   `BookProof.NavierStokesFlow.LagrangianNS.cauchy_existsUnique` (psi : Fin n → ℂ) : ∃! y : ℝ → Fin n → ℂ, y 0 = psi ∧ ∀ t, HasDerivAt y ((Complex.I • L.hFull) *ᵥ y t) t
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesCauchy`.
--
--   `BookProof.NavierStokesFlow.LagrangianNS.cauchy_existsUnique` (psi : Fin n → ℂ) : ∃! y : ℝ → Fin n → ℂ, y 0 = psi ∧ ∀ t, HasDerivAt y ((Complex.I • L.hFull) *ᵥ y t) t
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.LagrangianNS.cauchy_existsUnique`.

-- Generated from ChapterNavierStokesCauchy.lean — theorem BookProof.NavierStokesFlow.LagrangianNS.cauchy_existsUnique
import Mathlib
import Definitions.Def_ChapterNavierStokesCauchy
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow


open scoped BigOperators Matrix Matrix.Norms.Operator

variable {n : ℕ}
variable {n : ℕ} (d : NSTruncation n)
variable (L : LagrangianNS n)

theorem BookProof.NavierStokesFlow.LagrangianNS.cauchy_existsUnique (psi : Fin n → ℂ) :
    ∃! y : ℝ → Fin n → ℂ,
      y 0 = psi ∧ ∀ t, HasDerivAt y ((Complex.I • L.hFull) *ᵥ y t) t := by sorry
