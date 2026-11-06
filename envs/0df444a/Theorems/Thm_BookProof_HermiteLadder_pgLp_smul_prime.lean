-- Prove2me | Theorems.Thm_BookProof_HermiteLadder_pgLp_smul_prime
-- name    : BookProof.HermiteLadder.pgLp_smul_prime
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T14:45:57.255286+00:00
-- url     : https://prove2.me/theorems/2e340a2d-75bc-4716-b256-0519f1b4c4b8
-- title:
--   BookProof.HermiteLadder.pgLp_smul'
-- statement:
--   BookProof.HermiteLadder.pgLp_smul'

-- Generated from ChapterHermiteLadderOrder.lean — theorem BookProof.HermiteLadder.pgLp_smul'
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterDegSchrodingerCore
import Mathlib
import Definitions.Def_ChapterHermiteLadderOrder
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterFockWeightedSchurEsa
import Definitions.Def_ChapterHermiteLadderShift
open BookProof.HermiteProductCore
open BookProof.HermiteLadder



open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs BookProof.DegSchrodinger
open scoped ENNReal

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteLadder.pgLp_smul_prime (c : ℂ) (p : MvPolynomial (Fin d) ℂ) : pgLp (c • p) = c • pgLp p := by sorry
