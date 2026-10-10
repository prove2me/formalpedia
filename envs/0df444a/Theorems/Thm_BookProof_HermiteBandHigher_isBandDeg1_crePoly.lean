-- Prove2me | Theorems.Thm_BookProof_HermiteBandHigher_isBandDeg1_crePoly
-- name    : BookProof.HermiteBandHigher.isBandDeg1_crePoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:05:15.980502+00:00
-- url     : https://prove2.me/theorems/bac5a854-615c-48ab-a255-29a1e6ed12c7
-- title:
--   `BookProof.HermiteBandHigher.isBandDeg1_crePoly` (i : Fin d) : IsBandDeg 1 (crePoly i)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteBandCalculusHigher`.
--
--   `BookProof.HermiteBandHigher.isBandDeg1_crePoly` (i : Fin d) : IsBandDeg 1 (crePoly i)
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteBandHigher.isBandDeg1_crePoly`.

-- Generated from ChapterHermiteBandCalculusHigher.lean — theorem BookProof.HermiteBandHigher.isBandDeg1_crePoly
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculusHigher
import Definitions.Def_ChapterHermiteProductBasis
open BookProof.HermiteProductBasis
open BookProof.HermiteBandHigher



noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HermiteBand BookProof.YangMillsHermite
open BookProof.NavierStokesFlow.DifferentialL2

variable {d : ℕ}

theorem BookProof.HermiteBandHigher.isBandDeg1_crePoly (i : Fin d) : IsBandDeg 1 (crePoly i) := by sorry
