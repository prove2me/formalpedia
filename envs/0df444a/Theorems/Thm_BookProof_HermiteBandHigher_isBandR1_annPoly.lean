-- Prove2me | Theorems.Thm_BookProof_HermiteBandHigher_isBandR1_annPoly
-- name    : BookProof.HermiteBandHigher.isBandR1_annPoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:04:39.909219+00:00
-- url     : https://prove2.me/theorems/1b661afc-22ba-4edc-afff-4fa2ee6c74fe
-- title:
--   `BookProof.HermiteBandHigher.isBandR1_annPoly` (i : Fin d) : IsBandR 1 1 (annPoly i)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteBandCalculusHigher`.
--
--   `BookProof.HermiteBandHigher.isBandR1_annPoly` (i : Fin d) : IsBandR 1 1 (annPoly i)
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteBandHigher.isBandR1_annPoly`.

-- Generated from ChapterHermiteBandCalculusHigher.lean — theorem BookProof.HermiteBandHigher.isBandR1_annPoly
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

theorem BookProof.HermiteBandHigher.isBandR1_annPoly (i : Fin d) : IsBandR 1 1 (annPoly i) := by sorry
