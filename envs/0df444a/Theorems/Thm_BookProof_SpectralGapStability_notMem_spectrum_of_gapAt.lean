-- Prove2me | Theorems.Thm_BookProof_SpectralGapStability_notMem_spectrum_of_gapAt
-- name    : BookProof.SpectralGapStability.notMem_spectrum_of_gapAt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:57:33.857064+00:00
-- url     : https://prove2.me/theorems/77462c82-08d7-4b53-8f49-587f0cd0c070
-- title:
--   `BookProof.SpectralGapStability.notMem_spectrum_of_gapAt` {A : F →L[ℂ] F} (hA : IsSelfAdjoint A) {lam d : ℝ} (hd : 0 < d) (h : GapAt A lam d) : (lam : ℂ) ∉ spectrum ℂ A
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSpectralGapStability`.
--
--   `BookProof.SpectralGapStability.notMem_spectrum_of_gapAt` {A : F →L[ℂ] F} (hA : IsSelfAdjoint A) {lam d : ℝ} (hd : 0 < d) (h : GapAt A lam d) : (lam : ℂ) ∉ spectrum ℂ A
--
--   Formalization note: Lean 4 identifier `BookProof.SpectralGapStability.notMem_spectrum_of_gapAt`.

-- Generated from ChapterSpectralGapStability.lean — theorem BookProof.SpectralGapStability.notMem_spectrum_of_gapAt
import Mathlib
import Definitions.Def_ChapterSpectralGapStability
open BookProof.SpectralGapStability


noncomputable section


open scoped InnerProductSpace
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.SpectralGapStability.notMem_spectrum_of_gapAt {A : F →L[ℂ] F} (hA : IsSelfAdjoint A) {lam d : ℝ}
    (hd : 0 < d) (h : GapAt A lam d) : (lam : ℂ) ∉ spectrum ℂ A := by sorry
