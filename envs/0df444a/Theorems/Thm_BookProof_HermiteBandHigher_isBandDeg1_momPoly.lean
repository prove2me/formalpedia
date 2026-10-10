-- Prove2me | Theorems.Thm_BookProof_HermiteBandHigher_isBandDeg1_momPoly
-- name    : BookProof.HermiteBandHigher.isBandDeg1_momPoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:05:44.739354+00:00
-- url     : https://prove2.me/theorems/3a524879-4cb5-4afe-adad-3fa80d3baa0f
-- title:
--   `BookProof.HermiteBandHigher.isBandDeg1_momPoly` (i : Fin d) : IsBandDeg 1 (momPoly i)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteBandCalculusHigher`.
--
--   `BookProof.HermiteBandHigher.isBandDeg1_momPoly` (i : Fin d) : IsBandDeg 1 (momPoly i)
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteBandHigher.isBandDeg1_momPoly`.

-- Generated from ChapterHermiteBandCalculusHigher.lean — theorem BookProof.HermiteBandHigher.isBandDeg1_momPoly
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterYangMillsHermite
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculusHigher
import Definitions.Def_ChapterNavierStokesDifferentialL2
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteBandHigher



noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HermiteBand BookProof.YangMillsHermite
open BookProof.NavierStokesFlow.DifferentialL2

variable {d : ℕ}

theorem BookProof.HermiteBandHigher.isBandDeg1_momPoly (i : Fin d) : IsBandDeg 1 (momPoly i) := by sorry
