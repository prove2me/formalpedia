-- Prove2me | Theorems.Thm_BookProof_SqueezedGaussStates_sqCoef_of_le
-- name    : BookProof.SqueezedGaussStates.sqCoef_of_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:24:24.028986+00:00
-- url     : https://prove2.me/theorems/30c2ea81-e24f-4529-9e9a-aa2f6d3c1508
-- title:
--   `BookProof.SqueezedGaussStates.sqCoef_of_le` {v : ℝ} {M m : ℕ} (h : m ≤ M) : sqCoef v M m = v ^ m / (m.factorial : ℝ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSqueezedGaussStates`.
--
--   `BookProof.SqueezedGaussStates.sqCoef_of_le` {v : ℝ} {M m : ℕ} (h : m ≤ M) : sqCoef v M m = v ^ m / (m.factorial : ℝ)
--
--   Formalization note: Lean 4 identifier `BookProof.SqueezedGaussStates.sqCoef_of_le`.

-- Generated from ChapterSqueezedGaussStates.lean — theorem BookProof.SqueezedGaussStates.sqCoef_of_le
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterGaussCoordCombo
import Mathlib
import Definitions.Def_ChapterSqueezedGaussStates
open BookProof.SqueezedGaussStates



open MvPolynomial BookProof.HermiteProductCore BookProof.GaussCoordCombo

noncomputable section

variable {d : ℕ}

theorem BookProof.SqueezedGaussStates.sqCoef_of_le {v : ℝ} {M m : ℕ} (h : m ≤ M) :
    sqCoef v M m = v ^ m / (m.factorial : ℝ) := by sorry
