-- Prove2me | Theorems.Thm_BookProof_SqueezedGaussStates_op_squeezeState
-- name    : BookProof.SqueezedGaussStates.op_squeezeState
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:24:58.509986+00:00
-- url     : https://prove2.me/theorems/56b91e5b-5573-48ff-9492-408c6a4bc3c6
-- title:
--   `BookProof.SqueezedGaussStates.op_squeezeState` (i : Fin d) (α γ v : ℝ) (M : ℕ) : ((α : ℝ) : ℂ) • (X i * squeezeState i v M) + ((γ : ℝ) : ℂ) • pderiv i (squeezeState i v M) = coord
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSqueezedGaussStates`.
--
--   `BookProof.SqueezedGaussStates.op_squeezeState` (i : Fin d) (α γ v : ℝ) (M : ℕ) : ((α : ℝ) : ℂ) • (X i * squeezeState i v M) + ((γ : ℝ) : ℂ) • pderiv i (squeezeState i v M) = coordCombo i (opCoef α γ v M) 1 M
--
--   Formalization note: Lean 4 identifier `BookProof.SqueezedGaussStates.op_squeezeState`.

-- Generated from ChapterSqueezedGaussStates.lean — theorem BookProof.SqueezedGaussStates.op_squeezeState
import Definitions.Def_ChapterHermiteProductCore
import Mathlib
import Definitions.Def_ChapterSqueezedGaussStates
import Definitions.Def_ChapterGaussCoordCombo
open BookProof.GaussCoordCombo
open BookProof.SqueezedGaussStates



open MvPolynomial BookProof.HermiteProductCore BookProof.GaussCoordCombo

noncomputable section

variable {d : ℕ}

theorem BookProof.SqueezedGaussStates.op_squeezeState (i : Fin d) (α γ v : ℝ) (M : ℕ) :
    ((α : ℝ) : ℂ) • (X i * squeezeState i v M)
        + ((γ : ℝ) : ℂ) • pderiv i (squeezeState i v M)
      = coordCombo i (opCoef α γ v M) 1 M := by sorry
