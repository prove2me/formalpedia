-- Prove2me | Theorems.Thm_BookProof_SqueezedGaussStates_tendsto_boundary
-- name    : BookProof.SqueezedGaussStates.tendsto_boundary
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:44:20.998005+00:00
-- url     : https://prove2.me/theorems/60264b29-ca0f-42e9-822d-084b5dae7196
-- title:
--   `BookProof.SqueezedGaussStates.tendsto_boundary` (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ < 1) : Filter.Tendsto (fun M : ℕ => (2 * (M : ℝ) + 1) * ρ ^ M) Filter.atTop (nhds 0)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSqueezedGaussStates`.
--
--   `BookProof.SqueezedGaussStates.tendsto_boundary` (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ < 1) : Filter.Tendsto (fun M : ℕ => (2 * (M : ℝ) + 1) * ρ ^ M) Filter.atTop (nhds 0)
--
--   Formalization note: Lean 4 identifier `BookProof.SqueezedGaussStates.tendsto_boundary`.

-- Generated from ChapterSqueezedGaussStates.lean — theorem BookProof.SqueezedGaussStates.tendsto_boundary
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterGaussCoordCombo
import Mathlib
import Definitions.Def_ChapterSqueezedGaussStates
open BookProof.SqueezedGaussStates



open MvPolynomial BookProof.HermiteProductCore BookProof.GaussCoordCombo

noncomputable section

variable {d : ℕ}

theorem BookProof.SqueezedGaussStates.tendsto_boundary (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    Filter.Tendsto (fun M : ℕ => (2 * (M : ℝ) + 1) * ρ ^ M) Filter.atTop (nhds 0) := by sorry
