-- Prove2me | Theorems.Thm_BookProof_SqueezedGaussStates_opCoef_of_lt
-- name    : BookProof.SqueezedGaussStates.opCoef_of_lt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:24:21.745993+00:00
-- url     : https://prove2.me/theorems/be3b15a7-2995-415f-8714-74a647845fa4
-- title:
--   `BookProof.SqueezedGaussStates.opCoef_of_lt` (α γ v : ℝ) {M k : ℕ} (hk : k < M) : opCoef α γ v M k = kappa α γ v * sqCoef v M k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSqueezedGaussStates`.
--
--   `BookProof.SqueezedGaussStates.opCoef_of_lt` (α γ v : ℝ) {M k : ℕ} (hk : k < M) : opCoef α γ v M k = kappa α γ v * sqCoef v M k
--
--   Formalization note: Lean 4 identifier `BookProof.SqueezedGaussStates.opCoef_of_lt`.

-- Generated from ChapterSqueezedGaussStates.lean — theorem BookProof.SqueezedGaussStates.opCoef_of_lt
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterGaussCoordCombo
import Mathlib
import Definitions.Def_ChapterSqueezedGaussStates
open BookProof.SqueezedGaussStates



open MvPolynomial BookProof.HermiteProductCore BookProof.GaussCoordCombo

noncomputable section

variable {d : ℕ}

theorem BookProof.SqueezedGaussStates.opCoef_of_lt (α γ v : ℝ) {M k : ℕ} (hk : k < M) :
    opCoef α γ v M k = kappa α γ v * sqCoef v M k := by sorry
