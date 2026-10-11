-- Prove2me | Theorems.Thm_BookProof_SpectralGapStability_gapAt_perturb
-- name    : BookProof.SpectralGapStability.gapAt_perturb
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:57:01.004588+00:00
-- url     : https://prove2.me/theorems/cca31690-298d-4637-be95-df59326dbf10
-- title:
--   `BookProof.SpectralGapStability.gapAt_perturb` {A B : F →L[ℂ] F} {lam d eps : ℝ} (h : GapAt A lam d) (hAB : ‖A - B‖ ≤ eps) : GapAt B lam (d - eps)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSpectralGapStability`.
--
--   `BookProof.SpectralGapStability.gapAt_perturb` {A B : F →L[ℂ] F} {lam d eps : ℝ} (h : GapAt A lam d) (hAB : ‖A - B‖ ≤ eps) : GapAt B lam (d - eps)
--
--   Formalization note: Lean 4 identifier `BookProof.SpectralGapStability.gapAt_perturb`.

-- Generated from ChapterSpectralGapStability.lean — theorem BookProof.SpectralGapStability.gapAt_perturb
import Mathlib
import Definitions.Def_ChapterSpectralGapStability
open BookProof.SpectralGapStability


noncomputable section


open scoped InnerProductSpace
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.SpectralGapStability.gapAt_perturb {A B : F →L[ℂ] F} {lam d eps : ℝ}
    (h : GapAt A lam d) (hAB : ‖A - B‖ ≤ eps) : GapAt B lam (d - eps) := by sorry
