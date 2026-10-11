-- Prove2me | Theorems.Thm_BookProof_SpectralGapStability_spectrum_disjoint_of_shifted_square_bound
-- name    : BookProof.SpectralGapStability.spectrum_disjoint_of_shifted_square_bound
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:57:34.383978+00:00
-- url     : https://prove2.me/theorems/6178429a-72ea-493d-bfc3-8e108ac90ce5
-- title:
--   `BookProof.SpectralGapStability.spectrum_disjoint_of_shifted_square_bound` {A : F →L[ℂ] F} (hA : IsSelfAdjoint A) {c q : ℝ} (hq : 0 < q) (hbound : ∀ x : F, q * ‖x‖ ^ 2 ≤ ‖(A - (c :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSpectralGapStability`.
--
--   `BookProof.SpectralGapStability.spectrum_disjoint_of_shifted_square_bound` {A : F →L[ℂ] F} (hA : IsSelfAdjoint A) {c q : ℝ} (hq : 0 < q) (hbound : ∀ x : F, q * ‖x‖ ^ 2 ≤ ‖(A - (c : ℂ) • (1 : F →L[ℂ] F)) x‖ ^ 2) : ∀ lam ∈ Set.Ioo (c - Real.sqrt q) (c + Real.sqrt q), (lam : ℂ) ∉ spectrum ℂ A
--
--   Formalization note: Lean 4 identifier `BookProof.SpectralGapStability.spectrum_disjoint_of_shifted_square_bound`.

-- Generated from ChapterSpectralGapStability.lean — theorem BookProof.SpectralGapStability.spectrum_disjoint_of_shifted_square_bound
import Mathlib
import Definitions.Def_ChapterSpectralGapStability
open BookProof.SpectralGapStability


noncomputable section


open scoped InnerProductSpace
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.SpectralGapStability.spectrum_disjoint_of_shifted_square_bound {A : F →L[ℂ] F} (hA : IsSelfAdjoint A)
    {c q : ℝ} (hq : 0 < q)
    (hbound : ∀ x : F, q * ‖x‖ ^ 2 ≤ ‖(A - (c : ℂ) • (1 : F →L[ℂ] F)) x‖ ^ 2) :
    ∀ lam ∈ Set.Ioo (c - Real.sqrt q) (c + Real.sqrt q),
      (lam : ℂ) ∉ spectrum ℂ A := by sorry
