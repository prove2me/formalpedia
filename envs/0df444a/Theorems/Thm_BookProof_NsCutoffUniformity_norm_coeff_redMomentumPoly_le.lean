-- Prove2me | Theorems.Thm_BookProof_NsCutoffUniformity_norm_coeff_redMomentumPoly_le
-- name    : BookProof.NsCutoffUniformity.norm_coeff_redMomentumPoly_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-03T22:17:15.307195+00:00
-- url     : https://prove2.me/theorems/d3e16f92-eb41-42a1-bcce-2fe6fa5250c2
-- title:
--   `BookProof.NsCutoffUniformity.norm_coeff_redMomentumPoly_le` {Λ : ℝ} {k : Fin 3 → ℝ} (hk : ∀ j, |k j| ≤ Λ) (p : Fin n) (m : Fin (n * 6) →₀ ℕ) : ‖coeff m (redMomentumPoly k n...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsCutoffUniformity`.
--
--   `BookProof.NsCutoffUniformity.norm_coeff_redMomentumPoly_le` {Λ : ℝ} {k : Fin 3 → ℝ} (hk : ∀ j, |k j| ≤ Λ) (p : Fin n) (m : Fin (n * 6) →₀ ℕ) : ‖coeff m (redMomentumPoly k n p)‖ ≤ 3 * Λ
--
--   Formalization note: Lean 4 identifier `BookProof.NsCutoffUniformity.norm_coeff_redMomentumPoly_le`.

-- Generated from ChapterNsCutoffUniformity.lean — theorem BookProof.NsCutoffUniformity.norm_coeff_redMomentumPoly_le
import Definitions.Def_ChapterNavierStokesFullEulerianFock
import Mathlib
import Definitions.Def_ChapterNsCutoffUniformity



open MvPolynomial BookProof.NsFullEuler

noncomputable section

variable {n : ℕ}

variable {ι : Type*}

theorem BookProof.NsCutoffUniformity.norm_coeff_redMomentumPoly_le {Λ : ℝ} {k : Fin 3 → ℝ}
    (hk : ∀ j, |k j| ≤ Λ) (p : Fin n) (m : Fin (n * 6) →₀ ℕ) :
    ‖coeff m (redMomentumPoly k n p)‖ ≤ 3 * Λ := by sorry
