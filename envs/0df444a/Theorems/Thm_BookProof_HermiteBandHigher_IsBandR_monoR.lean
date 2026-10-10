-- Prove2me | Theorems.Thm_BookProof_HermiteBandHigher_IsBandR_monoR
-- name    : BookProof.HermiteBandHigher.IsBandR.monoR
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:04:03.094989+00:00
-- url     : https://prove2.me/theorems/3c7b574a-a5cf-42c3-bd48-ef93cd47c023
-- title:
--   `BookProof.HermiteBandHigher.IsBandR.monoR` {r r' m : ℕ} {T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} (hr : r ≤ r') (h : IsBandR r m T) : IsBandR r' m T
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteBandCalculusHigher`.
--
--   `BookProof.HermiteBandHigher.IsBandR.monoR` {r r' m : ℕ} {T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} (hr : r ≤ r') (h : IsBandR r m T) : IsBandR r' m T
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteBandHigher.IsBandR.monoR`.

-- Generated from ChapterHermiteBandCalculusHigher.lean — theorem BookProof.HermiteBandHigher.IsBandR.monoR
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

theorem BookProof.HermiteBandHigher.IsBandR.monoR {r r' m : ℕ} {T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ}
    (hr : r ≤ r') (h : IsBandR r m T) : IsBandR r' m T := by sorry
