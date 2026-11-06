-- Prove2me | Theorems.Thm_BookProof_NsCutoffUniformity_norm_coeff_redAdvectPoly_le
-- name    : BookProof.NsCutoffUniformity.norm_coeff_redAdvectPoly_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-03T22:16:35.590063+00:00
-- url     : https://prove2.me/theorems/6968f1a4-678e-4f49-82ae-cb92d9a757c5
-- title:
--   `BookProof.NsCutoffUniformity.norm_coeff_redAdvectPoly_le` {Λ : ℝ} {k : Fin 3 → ℝ} (hk : ∀ j, |k j| ≤ Λ) (p : Fin n) (i : Fin 3) (m : Fin (n * 6) →₀ ℕ) : ‖coeff m (redAdvectPoly k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsCutoffUniformity`.
--
--   `BookProof.NsCutoffUniformity.norm_coeff_redAdvectPoly_le` {Λ : ℝ} {k : Fin 3 → ℝ} (hk : ∀ j, |k j| ≤ Λ) (p : Fin n) (i : Fin 3) (m : Fin (n * 6) →₀ ℕ) : ‖coeff m (redAdvectPoly k n p i)‖ ≤ 3 * Λ
--
--   Formalization note: Lean 4 identifier `BookProof.NsCutoffUniformity.norm_coeff_redAdvectPoly_le`.

-- Generated from ChapterNsCutoffUniformity.lean — theorem BookProof.NsCutoffUniformity.norm_coeff_redAdvectPoly_le
import Definitions.Def_ChapterNavierStokesFullEulerianFock
import Mathlib
import Definitions.Def_ChapterNsCutoffUniformity



open MvPolynomial BookProof.NsFullEuler

noncomputable section

variable {n : ℕ}

variable {ι : Type*}

theorem BookProof.NsCutoffUniformity.norm_coeff_redAdvectPoly_le {Λ : ℝ} {k : Fin 3 → ℝ}
    (hk : ∀ j, |k j| ≤ Λ) (p : Fin n) (i : Fin 3) (m : Fin (n * 6) →₀ ℕ) :
    ‖coeff m (redAdvectPoly k n p i)‖ ≤ 3 * Λ := by sorry
