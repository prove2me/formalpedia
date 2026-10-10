-- Prove2me | Theorems.Thm_BookProof_HermiteBandHigher_isBand1_isBandR_one
-- name    : BookProof.HermiteBandHigher.isBand1_isBandR_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:04:14.201801+00:00
-- url     : https://prove2.me/theorems/86d3eda3-ae87-414e-9ad6-608332f6b3b9
-- title:
--   `BookProof.HermiteBandHigher.isBand1_isBandR_one` {T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} : IsBand1 T → IsBandR 1 1 T
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteBandCalculusHigher`.
--
--   `BookProof.HermiteBandHigher.isBand1_isBandR_one` {T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} : IsBand1 T → IsBandR 1 1 T
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteBandHigher.isBand1_isBandR_one`.

-- Generated from ChapterHermiteBandCalculusHigher.lean — theorem BookProof.HermiteBandHigher.isBand1_isBandR_one
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculusHigher
import Definitions.Def_ChapterHermiteBandCalculus
open BookProof.HermiteBand
open BookProof.HermiteBandHigher



noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HermiteBand BookProof.YangMillsHermite
open BookProof.NavierStokesFlow.DifferentialL2

variable {d : ℕ}

theorem BookProof.HermiteBandHigher.isBand1_isBandR_one {T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} :
    IsBand1 T → IsBandR 1 1 T := by sorry
