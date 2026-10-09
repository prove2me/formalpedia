-- Prove2me | Theorems.Thm_BookProof_HermiteBandHigher_IsBandR_smul
-- name    : BookProof.HermiteBandHigher.IsBandR.smul
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:04:04.388103+00:00
-- url     : https://prove2.me/theorems/2c2c6cbb-d59b-477d-b92d-fe726e8fb145
-- title:
--   `BookProof.HermiteBandHigher.IsBandR.smul` {r m : ℕ} {T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} (c : ℂ) (hT : IsBandR r m T) : IsBandR r m (c • T)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteBandCalculusHigher`.
--
--   `BookProof.HermiteBandHigher.IsBandR.smul` {r m : ℕ} {T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} (c : ℂ) (hT : IsBandR r m T) : IsBandR r m (c • T)
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteBandHigher.IsBandR.smul`.

-- Generated from ChapterHermiteBandCalculusHigher.lean — theorem BookProof.HermiteBandHigher.IsBandR.smul
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

theorem BookProof.HermiteBandHigher.IsBandR.smul {r m : ℕ} {T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ}
    (c : ℂ) (hT : IsBandR r m T) : IsBandR r m (c • T) := by sorry
