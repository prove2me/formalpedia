-- Prove2me | Theorems.Thm_BookProof_HermiteBandHigher_IsBandDeg_le
-- name    : BookProof.HermiteBandHigher.IsBandDeg.le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:02:00.486188+00:00
-- url     : https://prove2.me/theorems/218404fe-88f5-438f-87bc-778033837a08
-- title:
--   `BookProof.HermiteBandHigher.IsBandDeg.le` {m m' : ℕ} {T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} (hm : m ≤ m') (h : IsBandDeg m T) : IsBandDeg m' T
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteBandCalculusHigher`.
--
--   `BookProof.HermiteBandHigher.IsBandDeg.le` {m m' : ℕ} {T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} (hm : m ≤ m') (h : IsBandDeg m T) : IsBandDeg m' T
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteBandHigher.IsBandDeg.le`.

-- Generated from ChapterHermiteBandCalculusHigher.lean — theorem BookProof.HermiteBandHigher.IsBandDeg.le
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

theorem BookProof.HermiteBandHigher.IsBandDeg.le {m m' : ℕ} {T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ}
    (hm : m ≤ m') (h : IsBandDeg m T) : IsBandDeg m' T := by sorry
