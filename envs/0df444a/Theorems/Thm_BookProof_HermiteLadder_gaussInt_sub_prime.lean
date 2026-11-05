-- Prove2me | Theorems.Thm_BookProof_HermiteLadder_gaussInt_sub_prime
-- name    : BookProof.HermiteLadder.gaussInt_sub_prime
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T14:45:49.702146+00:00
-- url     : https://prove2.me/theorems/121b3e12-a24c-4917-8e61-5a7a339e19b4
-- title:
--   BookProof.HermiteLadder.gaussInt_sub'
-- statement:
--   BookProof.HermiteLadder.gaussInt_sub'

-- Generated from ChapterHermiteLadderOrder.lean — theorem BookProof.HermiteLadder.gaussInt_sub'
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

theorem BookProof.HermiteLadder.gaussInt_sub_prime (r s : MvPolynomial (Fin d) ℂ) :
    gaussInt (r - s) = gaussInt r - gaussInt s := by sorry
