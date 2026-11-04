-- Prove2me | Theorems.Thm_BookProof_NsCutoffUniformity_norm_coeff_redFormPoly_unbounded_of_no_cutoff
-- name    : BookProof.NsCutoffUniformity.norm_coeff_redFormPoly_unbounded_of_no_cutoff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T01:59:50.699191+00:00
-- url     : https://prove2.me/theorems/4709a659-9dc9-4301-affb-ff1fcfed7b85
-- title:
--   `BookProof.NsCutoffUniformity.norm_coeff_redFormPoly_unbounded_of_no_cutoff` (nu : ℝ) (C₀ : ℝ) : ∃ (k : Fin 3 → ℝ) (m : Fin (1 * 6) →₀ ℕ) (p : Fin 1) (r : Fin 7), C₀ <...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsCutoffUniformity`.
--
--   `BookProof.NsCutoffUniformity.norm_coeff_redFormPoly_unbounded_of_no_cutoff` (nu : ℝ) (C₀ : ℝ) : ∃ (k : Fin 3 → ℝ) (m : Fin (1 * 6) →₀ ℕ) (p : Fin 1) (r : Fin 7), C₀ < ‖coeff m (redFormPoly nu k 1 p r)‖
--
--   Formalization note: Lean 4 identifier `BookProof.NsCutoffUniformity.norm_coeff_redFormPoly_unbounded_of_no_cutoff`.

-- Generated from ChapterNsCutoffUniformity.lean — theorem BookProof.NsCutoffUniformity.norm_coeff_redFormPoly_unbounded_of_no_cutoff
import Definitions.Def_ChapterNavierStokesFullEulerianFock
import Mathlib
import Definitions.Def_ChapterNsCutoffUniformity



open MvPolynomial BookProof.NsFullEuler

noncomputable section

variable {n : ℕ}

variable {ι : Type*}

theorem BookProof.NsCutoffUniformity.norm_coeff_redFormPoly_unbounded_of_no_cutoff (nu : ℝ) (C₀ : ℝ) :
    ∃ (k : Fin 3 → ℝ) (m : Fin (1 * 6) →₀ ℕ) (p : Fin 1) (r : Fin 7),
      C₀ < ‖coeff m (redFormPoly nu k 1 p r)‖ := by sorry
