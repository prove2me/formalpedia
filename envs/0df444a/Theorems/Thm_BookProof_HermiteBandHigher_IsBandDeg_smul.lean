-- Prove2me | Theorems.Thm_BookProof_HermiteBandHigher_IsBandDeg_smul
-- name    : BookProof.HermiteBandHigher.IsBandDeg.smul
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:02:27.271461+00:00
-- url     : https://prove2.me/theorems/2746a3b5-3daf-4a73-a10e-aff4597bd8eb
-- title:
--   `BookProof.HermiteBandHigher.IsBandDeg.smul` {m : ℕ} {T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} (c : ℂ) (hT : IsBandDeg m T) : IsBandDeg m (c • T)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteBandCalculusHigher`.
--
--   `BookProof.HermiteBandHigher.IsBandDeg.smul` {m : ℕ} {T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} (c : ℂ) (hT : IsBandDeg m T) : IsBandDeg m (c • T)
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteBandHigher.IsBandDeg.smul`.

-- Generated from ChapterHermiteBandCalculusHigher.lean — theorem BookProof.HermiteBandHigher.IsBandDeg.smul
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculusHigher
open BookProof.HermiteBandHigher



noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HermiteBand BookProof.YangMillsHermite
open BookProof.NavierStokesFlow.DifferentialL2

variable {d : ℕ}

theorem BookProof.HermiteBandHigher.IsBandDeg.smul {m : ℕ} {T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ}
    (c : ℂ) (hT : IsBandDeg m T) : IsBandDeg m (c • T) := by sorry
