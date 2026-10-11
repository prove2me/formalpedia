-- Prove2me | Theorems.Thm_BookProof_SpectralGapStability_spectrum_disjoint_of_uniform_window
-- name    : BookProof.SpectralGapStability.spectrum_disjoint_of_uniform_window
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:57:43.40285+00:00
-- url     : https://prove2.me/theorems/d6ac12c8-52c3-4546-90ad-9a2bcff84fc3
-- title:
--   `BookProof.SpectralGapStability.spectrum_disjoint_of_uniform_window` {A : ℕ → F →L[ℂ] F} {B : F →L[ℂ] F} (hB : IsSelfAdjoint B) {a b : ℝ} (hgap : ∀ lam ∈ Set.Ioo a b, ∀ m, GapAt (A
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSpectralGapStability`.
--
--   `BookProof.SpectralGapStability.spectrum_disjoint_of_uniform_window` {A : ℕ → F →L[ℂ] F} {B : F →L[ℂ] F} (hB : IsSelfAdjoint B) {a b : ℝ} (hgap : ∀ lam ∈ Set.Ioo a b, ∀ m, GapAt (A m) lam (min (lam - a) (b - lam))) (hconv : Tendsto (fun m => ‖A m - B‖) atTop (𝓝 0)) : ∀ lam ∈ Set.Ioo a b, (lam : ℂ) ∉ spectrum ℂ B
--
--   Formalization note: Lean 4 identifier `BookProof.SpectralGapStability.spectrum_disjoint_of_uniform_window`.

-- Generated from ChapterSpectralGapStability.lean — theorem BookProof.SpectralGapStability.spectrum_disjoint_of_uniform_window
import Mathlib
import Definitions.Def_ChapterSpectralGapStability
open BookProof.SpectralGapStability


noncomputable section


open scoped InnerProductSpace
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.SpectralGapStability.spectrum_disjoint_of_uniform_window {A : ℕ → F →L[ℂ] F} {B : F →L[ℂ] F}
    (hB : IsSelfAdjoint B) {a b : ℝ}
    (hgap : ∀ lam ∈ Set.Ioo a b, ∀ m, GapAt (A m) lam (min (lam - a) (b - lam)))
    (hconv : Tendsto (fun m => ‖A m - B‖) atTop (𝓝 0)) :
    ∀ lam ∈ Set.Ioo a b, (lam : ℂ) ∉ spectrum ℂ B := by sorry
