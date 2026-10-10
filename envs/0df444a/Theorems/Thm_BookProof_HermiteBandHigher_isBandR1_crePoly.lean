-- Prove2me | Theorems.Thm_BookProof_HermiteBandHigher_isBandR1_crePoly
-- name    : BookProof.HermiteBandHigher.isBandR1_crePoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:04:33.590473+00:00
-- url     : https://prove2.me/theorems/88945706-ffaa-4963-a8c0-bedeedce8c96
-- title:
--   `BookProof.HermiteBandHigher.isBandR1_crePoly` (i : Fin d) : IsBandR 1 1 (crePoly i)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteBandCalculusHigher`.
--
--   `BookProof.HermiteBandHigher.isBandR1_crePoly` (i : Fin d) : IsBandR 1 1 (crePoly i)
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteBandHigher.isBandR1_crePoly`.

-- Generated from ChapterHermiteBandCalculusHigher.lean — theorem BookProof.HermiteBandHigher.isBandR1_crePoly
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

theorem BookProof.HermiteBandHigher.isBandR1_crePoly (i : Fin d) : IsBandR 1 1 (crePoly i) := by sorry
