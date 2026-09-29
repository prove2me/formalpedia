-- Prove2me | Theorems.Thm_BookProof_SirkFinitePrecision_ground_ge_of_no_eigenvalue_below
-- name    : BookProof.SirkFinitePrecision.ground_ge_of_no_eigenvalue_below
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T14:49:07.796463+00:00
-- url     : https://prove2.me/theorems/0c80fb40-74da-4cdd-a41b-2f84d9c011f0
-- title:
--   The second, purely a-posteriori route to a lower bound: if the computed Ritz set certifies that no eigenvalue lies below `θ − r`, then the lowest eigenvalue is bracketed from below as well
-- statement:
--   The second, purely a-posteriori route to a lower bound: if the computed Ritz set
--   certifies that no eigenvalue lies below `θ − r`, then the lowest eigenvalue is
--   bracketed from below as well.  (Stated as the trivial specialisation it is: the
--   content is that the hypothesis, not the residual alone, is what licenses the
--   lower bound.)
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.SirkFinitePrecision.ground_ge_of_no_eigenvalue_below` (module `BookProof.SirkFinitePrecision`), line-linked source: `ChapterSirkFinitePrecision.lean` lines 297–307.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkFinitePrecision.lean#L297-L307

-- Generated from ChapterSirkFinitePrecision.lean — theorem BookProof.SirkFinitePrecision.ground_ge_of_no_eigenvalue_below
import Mathlib
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.SirkFinitePrecision






noncomputable section


open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

theorem BookProof.SirkFinitePrecision.ground_ge_of_no_eigenvalue_below {T : E →ₗ[ℂ] E} {lam0 θ r : ℝ}
    (hlam0 : HasRealEigenvalue T lam0)
    (hnone : ∀ lam : ℝ, HasRealEigenvalue T lam → θ - r ≤ lam) :
    θ - r ≤ lam0 := by sorry
