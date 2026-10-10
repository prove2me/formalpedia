-- Prove2me | Theorems.Thm_BookProof_HermiteBandHigher_mulOp_smul
-- name    : BookProof.HermiteBandHigher.mulOp_smul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:07:15.216639+00:00
-- url     : https://prove2.me/theorems/a979d3c0-a03d-432e-b7a4-a5a1e06062c8
-- title:
--   `BookProof.HermiteBandHigher.mulOp_smul` (c : ℂ) (f : MvPolynomial (Fin d) ℂ) : mulOp (c • f) = c • mulOp f
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteBandCalculusHigher`.
--
--   `BookProof.HermiteBandHigher.mulOp_smul` (c : ℂ) (f : MvPolynomial (Fin d) ℂ) : mulOp (c • f) = c • mulOp f
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteBandHigher.mulOp_smul`.

-- Generated from ChapterHermiteBandCalculusHigher.lean — theorem BookProof.HermiteBandHigher.mulOp_smul
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculusHigher
import Definitions.Def_ChapterF7
open BookProof.ChapterF7
open BookProof.HermiteBandHigher



noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HermiteBand BookProof.YangMillsHermite
open BookProof.NavierStokesFlow.DifferentialL2

variable {d : ℕ}

theorem BookProof.HermiteBandHigher.mulOp_smul (c : ℂ) (f : MvPolynomial (Fin d) ℂ) : mulOp (c • f) = c • mulOp f := by sorry
