-- Prove2me | Theorems.Thm_BookProof_SqueezedGaussStates_pderiv_coordCombo_even
-- name    : BookProof.SqueezedGaussStates.pderiv_coordCombo_even
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:24:13.314599+00:00
-- url     : https://prove2.me/theorems/95f660b6-1d5e-4d02-9fcc-5808d10b85a0
-- title:
--   `BookProof.SqueezedGaussStates.pderiv_coordCombo_even` (i : Fin d) (a : ℕ → ℝ) (M : ℕ) (ha : a (M + 1) = 0) : pderiv i (coordCombo i a 0 M) = coordCombo i (fun k => 2 * (k + 1) * a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSqueezedGaussStates`.
--
--   `BookProof.SqueezedGaussStates.pderiv_coordCombo_even` (i : Fin d) (a : ℕ → ℝ) (M : ℕ) (ha : a (M + 1) = 0) : pderiv i (coordCombo i a 0 M) = coordCombo i (fun k => 2 * (k + 1) * a (k + 1)) 1 M
--
--   Formalization note: Lean 4 identifier `BookProof.SqueezedGaussStates.pderiv_coordCombo_even`.

-- Generated from ChapterSqueezedGaussStates.lean — theorem BookProof.SqueezedGaussStates.pderiv_coordCombo_even
import Mathlib
import Definitions.Def_ChapterSqueezedGaussStates
import Definitions.Def_ChapterGaussCoordCombo
import Definitions.Def_ChapterHermiteProductCore
open BookProof.GaussCoordCombo
open BookProof.HermiteProductCore
open BookProof.SqueezedGaussStates



open MvPolynomial BookProof.HermiteProductCore BookProof.GaussCoordCombo

noncomputable section

variable {d : ℕ}

theorem BookProof.SqueezedGaussStates.pderiv_coordCombo_even (i : Fin d) (a : ℕ → ℝ) (M : ℕ) (ha : a (M + 1) = 0) :
    pderiv i (coordCombo i a 0 M) = coordCombo i (fun k => 2 * (k + 1) * a (k + 1)) 1 M := by sorry
