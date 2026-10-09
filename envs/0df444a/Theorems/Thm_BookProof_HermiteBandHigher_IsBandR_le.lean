-- Prove2me | Theorems.Thm_BookProof_HermiteBandHigher_IsBandR_le
-- name    : BookProof.HermiteBandHigher.IsBandR.le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:01:41.807225+00:00
-- url     : https://prove2.me/theorems/3ec8f7da-9d64-40a4-98c9-4d93e4b2278f
-- title:
--   `BookProof.HermiteBandHigher.IsBandR.le` {r m m' : ℕ} {T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} (hm : m ≤ m') (h : IsBandR r m T) : IsBandR r m' T
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteBandCalculusHigher`.
--
--   `BookProof.HermiteBandHigher.IsBandR.le` {r m m' : ℕ} {T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} (hm : m ≤ m') (h : IsBandR r m T) : IsBandR r m' T
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteBandHigher.IsBandR.le`.

-- Generated from ChapterHermiteBandCalculusHigher.lean — theorem BookProof.HermiteBandHigher.IsBandR.le
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

theorem BookProof.HermiteBandHigher.IsBandR.le {r m m' : ℕ} {T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ}
    (hm : m ≤ m') (h : IsBandR r m T) : IsBandR r m' T := by sorry
