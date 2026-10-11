-- Prove2me | Theorems.Thm_BookProof_SpectralGapStability_notMem_spectrum_of_uniform_gap
-- name    : BookProof.SpectralGapStability.notMem_spectrum_of_uniform_gap
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:57:21.357418+00:00
-- url     : https://prove2.me/theorems/a72067c5-242a-4290-ae82-91c8c84664b1
-- title:
--   `BookProof.SpectralGapStability.notMem_spectrum_of_uniform_gap` {A : ℕ → F →L[ℂ] F} {B : F →L[ℂ] F} (hB : IsSelfAdjoint B) {lam d : ℝ} (hd : 0 < d) (hgap : ∀ m, GapAt (A m) lam d)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSpectralGapStability`.
--
--   `BookProof.SpectralGapStability.notMem_spectrum_of_uniform_gap` {A : ℕ → F →L[ℂ] F} {B : F →L[ℂ] F} (hB : IsSelfAdjoint B) {lam d : ℝ} (hd : 0 < d) (hgap : ∀ m, GapAt (A m) lam d) (hconv : Tendsto (fun m => ‖A m - B‖) atTop (𝓝 0)) : (lam : ℂ) ∉ spectrum ℂ B
--
--   Formalization note: Lean 4 identifier `BookProof.SpectralGapStability.notMem_spectrum_of_uniform_gap`.

-- Generated from ChapterSpectralGapStability.lean — theorem BookProof.SpectralGapStability.notMem_spectrum_of_uniform_gap
import Mathlib
import Definitions.Def_ChapterSpectralGapStability
open BookProof.SpectralGapStability


noncomputable section


open scoped InnerProductSpace
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.SpectralGapStability.notMem_spectrum_of_uniform_gap {A : ℕ → F →L[ℂ] F} {B : F →L[ℂ] F}
    (hB : IsSelfAdjoint B) {lam d : ℝ} (hd : 0 < d) (hgap : ∀ m, GapAt (A m) lam d)
    (hconv : Tendsto (fun m => ‖A m - B‖) atTop (𝓝 0)) : (lam : ℂ) ∉ spectrum ℂ B := by sorry
