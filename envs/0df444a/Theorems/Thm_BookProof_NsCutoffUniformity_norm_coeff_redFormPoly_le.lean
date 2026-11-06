-- Prove2me | Theorems.Thm_BookProof_NsCutoffUniformity_norm_coeff_redFormPoly_le
-- name    : BookProof.NsCutoffUniformity.norm_coeff_redFormPoly_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-03T22:16:45.432314+00:00
-- url     : https://prove2.me/theorems/8dcf2736-109d-4667-9523-8f03b7bcb5ac
-- title:
--   `BookProof.NsCutoffUniformity.norm_coeff_redFormPoly_le` (nu : ℝ) {Λ : ℝ} {k : Fin 3 → ℝ} (hΛ : 0 ≤ Λ) (hk : ∀ j, |k j| ≤ Λ) (p : Fin n) (r : Fin 7) (m : Fin (n * 6) →₀ ℕ)...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsCutoffUniformity`.
--
--   `BookProof.NsCutoffUniformity.norm_coeff_redFormPoly_le` (nu : ℝ) {Λ : ℝ} {k : Fin 3 → ℝ} (hΛ : 0 ≤ Λ) (hk : ∀ j, |k j| ≤ Λ) (p : Fin n) (r : Fin 7) (m : Fin (n * 6) →₀ ℕ) : ‖coeff m (redFormPoly nu k n p r)‖ ≤ cutoffBound nu Λ
--
--   Formalization note: Lean 4 identifier `BookProof.NsCutoffUniformity.norm_coeff_redFormPoly_le`.

-- Generated from ChapterNsCutoffUniformity.lean — theorem BookProof.NsCutoffUniformity.norm_coeff_redFormPoly_le
import Definitions.Def_ChapterNavierStokesFullEulerianFock
import Mathlib
import Definitions.Def_ChapterNsCutoffUniformity



open MvPolynomial BookProof.NsFullEuler

noncomputable section

variable {n : ℕ}

variable {ι : Type*}

theorem BookProof.NsCutoffUniformity.norm_coeff_redFormPoly_le (nu : ℝ) {Λ : ℝ} {k : Fin 3 → ℝ} (hΛ : 0 ≤ Λ)
    (hk : ∀ j, |k j| ≤ Λ) (p : Fin n) (r : Fin 7) (m : Fin (n * 6) →₀ ℕ) :
    ‖coeff m (redFormPoly nu k n p r)‖ ≤ cutoffBound nu Λ := by sorry
