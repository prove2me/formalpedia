-- Prove2me | Theorems.Thm_BookProof_SpectralGapStability_exists_gapAt_of_notMem_spectrum
-- name    : BookProof.SpectralGapStability.exists_gapAt_of_notMem_spectrum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:57:24.46109+00:00
-- url     : https://prove2.me/theorems/f8c73e1c-435c-4158-9d34-d3b1c833f8fe
-- title:
--   `BookProof.SpectralGapStability.exists_gapAt_of_notMem_spectrum` {A : F →L[ℂ] F} {lam : ℝ} (h : (lam : ℂ) ∉ spectrum ℂ A) : ∃ d > 0, GapAt A lam d
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSpectralGapStability`.
--
--   `BookProof.SpectralGapStability.exists_gapAt_of_notMem_spectrum` {A : F →L[ℂ] F} {lam : ℝ} (h : (lam : ℂ) ∉ spectrum ℂ A) : ∃ d > 0, GapAt A lam d
--
--   Formalization note: Lean 4 identifier `BookProof.SpectralGapStability.exists_gapAt_of_notMem_spectrum`.

-- Generated from ChapterSpectralGapStability.lean — theorem BookProof.SpectralGapStability.exists_gapAt_of_notMem_spectrum
import Mathlib
import Definitions.Def_ChapterSpectralGapStability
open BookProof.SpectralGapStability


noncomputable section


open scoped InnerProductSpace
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.SpectralGapStability.exists_gapAt_of_notMem_spectrum {A : F →L[ℂ] F} {lam : ℝ}
    (h : (lam : ℂ) ∉ spectrum ℂ A) : ∃ d > 0, GapAt A lam d := by sorry
