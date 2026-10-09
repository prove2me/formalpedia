-- Prove2me | Theorems.Thm_BookProof_HermiteBandHigher_IsBandR_add
-- name    : BookProof.HermiteBandHigher.IsBandR.add
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:02:12.247594+00:00
-- url     : https://prove2.me/theorems/557b1a26-9219-401c-bd42-28405d4b5f79
-- title:
--   `BookProof.HermiteBandHigher.IsBandR.add` {r m : ℕ} {T S : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} (hT : IsBandR r m T) (hS : IsBandR r m S) : IsBandR r m (T + S)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteBandCalculusHigher`.
--
--   `BookProof.HermiteBandHigher.IsBandR.add` {r m : ℕ} {T S : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} (hT : IsBandR r m T) (hS : IsBandR r m S) : IsBandR r m (T + S)
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteBandHigher.IsBandR.add`.

-- Generated from ChapterHermiteBandCalculusHigher.lean — theorem BookProof.HermiteBandHigher.IsBandR.add
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculusHigher
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.HermiteBand
open BookProof.SirkFinitePrecision
open BookProof.SirkFinitePrecision.CertInterval
open BookProof.HermiteBandHigher



noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HermiteBand BookProof.YangMillsHermite
open BookProof.NavierStokesFlow.DifferentialL2

variable {d : ℕ}

theorem BookProof.HermiteBandHigher.IsBandR.add {r m : ℕ} {T S : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ}
    (hT : IsBandR r m T) (hS : IsBandR r m S) : IsBandR r m (T + S) := by sorry
