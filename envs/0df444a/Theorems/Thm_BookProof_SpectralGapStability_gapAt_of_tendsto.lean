-- Prove2me | Theorems.Thm_BookProof_SpectralGapStability_gapAt_of_tendsto
-- name    : BookProof.SpectralGapStability.gapAt_of_tendsto
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:57:19.085935+00:00
-- url     : https://prove2.me/theorems/81cee26e-9737-4d04-9ef4-726d9b76d5b1
-- title:
--   `BookProof.SpectralGapStability.gapAt_of_tendsto` {A : ℕ → F →L[ℂ] F} {B : F →L[ℂ] F} {lam d : ℝ} (hA : ∀ m, GapAt (A m) lam d) (hconv : Tendsto (fun m => ‖A m - B‖) atTop...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSpectralGapStability`.
--
--   `BookProof.SpectralGapStability.gapAt_of_tendsto` {A : ℕ → F →L[ℂ] F} {B : F →L[ℂ] F} {lam d : ℝ} (hA : ∀ m, GapAt (A m) lam d) (hconv : Tendsto (fun m => ‖A m - B‖) atTop (𝓝 0)) : GapAt B lam d
--
--   Formalization note: Lean 4 identifier `BookProof.SpectralGapStability.gapAt_of_tendsto`.

-- Generated from ChapterSpectralGapStability.lean — theorem BookProof.SpectralGapStability.gapAt_of_tendsto
import Mathlib
import Definitions.Def_ChapterSpectralGapStability
open BookProof.SpectralGapStability


noncomputable section


open scoped InnerProductSpace
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.SpectralGapStability.gapAt_of_tendsto {A : ℕ → F →L[ℂ] F} {B : F →L[ℂ] F} {lam d : ℝ}
    (hA : ∀ m, GapAt (A m) lam d)
    (hconv : Tendsto (fun m => ‖A m - B‖) atTop (𝓝 0)) : GapAt B lam d := by sorry
