-- Prove2me | Theorems.Thm_BookProof_HermiteBandHigher_isBandR1_mulXPoly
-- name    : BookProof.HermiteBandHigher.isBandR1_mulXPoly
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:04:44.975978+00:00
-- url     : https://prove2.me/theorems/ee07cc72-e905-4489-9b92-28589512c476
-- title:
--   `BookProof.HermiteBandHigher.isBandR1_mulXPoly` (i : Fin d) : IsBandR 1 1 (mulXPoly i)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteBandCalculusHigher`.
--
--   `BookProof.HermiteBandHigher.isBandR1_mulXPoly` (i : Fin d) : IsBandR 1 1 (mulXPoly i)
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteBandHigher.isBandR1_mulXPoly`.

-- Generated from ChapterHermiteBandCalculusHigher.lean — theorem BookProof.HermiteBandHigher.isBandR1_mulXPoly
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

theorem BookProof.HermiteBandHigher.isBandR1_mulXPoly (i : Fin d) : IsBandR 1 1 (mulXPoly i) := by sorry
