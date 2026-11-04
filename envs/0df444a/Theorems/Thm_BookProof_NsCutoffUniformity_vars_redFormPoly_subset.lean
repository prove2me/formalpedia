-- Prove2me | Theorems.Thm_BookProof_NsCutoffUniformity_vars_redFormPoly_subset
-- name    : BookProof.NsCutoffUniformity.vars_redFormPoly_subset
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-03T22:17:22.697863+00:00
-- url     : https://prove2.me/theorems/57c8c99c-4afd-4afa-93cd-864e6b0eac3e
-- title:
--   `BookProof.NsCutoffUniformity.vars_redFormPoly_subset` (nu : ℝ) (k : Fin 3 → ℝ) (p : Fin n) (r : Fin 7) : (redFormPoly nu k n p r).vars ⊆ Finset.image (redIdx p) Finset.univ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsCutoffUniformity`.
--
--   `BookProof.NsCutoffUniformity.vars_redFormPoly_subset` (nu : ℝ) (k : Fin 3 → ℝ) (p : Fin n) (r : Fin 7) : (redFormPoly nu k n p r).vars ⊆ Finset.image (redIdx p) Finset.univ
--
--   Formalization note: Lean 4 identifier `BookProof.NsCutoffUniformity.vars_redFormPoly_subset`.

-- Generated from ChapterNsCutoffUniformity.lean — theorem BookProof.NsCutoffUniformity.vars_redFormPoly_subset
import Definitions.Def_ChapterNavierStokesFullEulerianFock
import Mathlib
import Definitions.Def_ChapterNsCutoffUniformity



open MvPolynomial BookProof.NsFullEuler

noncomputable section

variable {n : ℕ}

variable {ι : Type*}
variable (nu : ℝ) (k : Fin 3 → ℝ)

theorem BookProof.NsCutoffUniformity.vars_redFormPoly_subset (nu : ℝ) (k : Fin 3 → ℝ) (p : Fin n) (r : Fin 7) :
    (redFormPoly nu k n p r).vars ⊆ Finset.image (redIdx p) Finset.univ := by sorry
