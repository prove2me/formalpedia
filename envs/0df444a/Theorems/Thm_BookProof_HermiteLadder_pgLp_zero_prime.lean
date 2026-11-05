-- Prove2me | Theorems.Thm_BookProof_HermiteLadder_pgLp_zero_prime
-- name    : BookProof.HermiteLadder.pgLp_zero_prime
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-04T14:46:06.976459+00:00
-- url     : https://prove2.me/theorems/b636fdb2-2b61-40eb-bd17-43b9da44e7a8
-- title:
--   BookProof.HermiteLadder.pgLp_zero'
-- statement:
--   BookProof.HermiteLadder.pgLp_zero'

-- Generated from ChapterHermiteLadderOrder.lean — theorem BookProof.HermiteLadder.pgLp_zero'
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

theorem BookProof.HermiteLadder.pgLp_zero_prime : pgLp (0 : MvPolynomial (Fin d) ℂ) = 0 := by sorry
