-- Prove2me | Theorems.Thm_BookProof_HermiteBandHigher_gpow_add
-- name    : BookProof.HermiteBandHigher.gpow_add
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:00:35.347974+00:00
-- url     : https://prove2.me/theorems/beaacb97-fffc-4ff5-a0f5-5e6773dbf01f
-- title:
--   `BookProof.HermiteBandHigher.gpow_add` (m m' n : ℕ) : gpow (m + m') n = gpow m n * gpow m' n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteBandCalculusHigher`.
--
--   `BookProof.HermiteBandHigher.gpow_add` (m m' n : ℕ) : gpow (m + m') n = gpow m n * gpow m' n
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteBandHigher.gpow_add`.

-- Generated from ChapterHermiteBandCalculusHigher.lean — theorem BookProof.HermiteBandHigher.gpow_add
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

theorem BookProof.HermiteBandHigher.gpow_add (m m' n : ℕ) : gpow (m + m') n = gpow m n * gpow m' n := by sorry
