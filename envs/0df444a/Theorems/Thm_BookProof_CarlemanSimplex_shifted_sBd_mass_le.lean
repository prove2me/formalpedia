-- Prove2me | Theorems.Thm_BookProof_CarlemanSimplex_shifted_sBd_mass_le
-- name    : BookProof.CarlemanSimplex.shifted_sBd_mass_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-07T22:49:05.156541+00:00
-- url     : https://prove2.me/theorems/9d71fe76-ae1d-4550-af39-a1c57a2b41fe
-- title:
--   `BookProof.CarlemanSimplex.shifted_sBd_mass_le` {B : ℝ} (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B) (P : Fin d →₀ ℕ) (M : ℕ) : ∑ N ∈ Finset.range...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanSimplex`.
--
--   `BookProof.CarlemanSimplex.shifted_sBd_mass_le` {B : ℝ} (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B) (P : Fin d →₀ ℕ) (M : ℕ) : ∑ N ∈ Finset.range M, ∑ a ∈ sBd d N (deg P), ‖u (a + P)‖ ^ 2 ≤ ((deg P : ℕ) : ℝ) * B
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanSimplex.shifted_sBd_mass_le`.

-- Generated from ChapterCarlemanSimplex.lean — theorem BookProof.CarlemanSimplex.shifted_sBd_mass_le
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Mathlib
import Definitions.Def_ChapterCarlemanSimplexPromoted
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.CarlemanSimplex



open Finset
open BookProof.HermiteCarleman BookProof.CarlemanTwoStep

noncomputable section

variable {d : ℕ}

variable {u : (Fin d →₀ ℕ) → ℂ}
variable {lam : (Fin d →₀ ℕ) → ℝ} {w : Fin d → ℂ} {W M : Fin d → Fin d → ℂ} {z : ℂ}

theorem BookProof.CarlemanSimplex.shifted_sBd_mass_le {B : ℝ}
    (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B) (P : Fin d →₀ ℕ) (M : ℕ) :
    ∑ N ∈ Finset.range M, ∑ a ∈ sBd d N (deg P), ‖u (a + P)‖ ^ 2 ≤ ((deg P : ℕ) : ℝ) * B := by sorry
