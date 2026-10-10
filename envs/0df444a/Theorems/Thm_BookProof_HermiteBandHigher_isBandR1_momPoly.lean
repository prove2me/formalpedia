-- Prove2me | Theorems.Thm_BookProof_HermiteBandHigher_isBandR1_momPoly
-- name    : BookProof.HermiteBandHigher.isBandR1_momPoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:09:21.719978+00:00
-- url     : https://prove2.me/theorems/d8bd6ea9-0dc1-4dd7-b0b1-4d6add3edd91
-- title:
--   `BookProof.HermiteBandHigher.isBandR1_momPoly` (i : Fin d) : IsBandR 1 1 (momPoly i)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteBandCalculusHigher`.
--
--   `BookProof.HermiteBandHigher.isBandR1_momPoly` (i : Fin d) : IsBandR 1 1 (momPoly i)
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteBandHigher.isBandR1_momPoly`.

-- Generated from ChapterHermiteBandCalculusHigher.lean — theorem BookProof.HermiteBandHigher.isBandR1_momPoly
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

theorem BookProof.HermiteBandHigher.isBandR1_momPoly (i : Fin d) : IsBandR 1 1 (momPoly i) := by sorry
