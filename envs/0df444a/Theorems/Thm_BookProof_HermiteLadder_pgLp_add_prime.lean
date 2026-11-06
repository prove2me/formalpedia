-- Prove2me | Theorems.Thm_BookProof_HermiteLadder_pgLp_add_prime
-- name    : BookProof.HermiteLadder.pgLp_add_prime
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T14:45:40.900381+00:00
-- url     : https://prove2.me/theorems/b5e6d3ab-e7ea-4ce3-85b0-4dc406b03e11
-- title:
--   BookProof.HermiteLadder.pgLp_add'
-- statement:
--   BookProof.HermiteLadder.pgLp_add'

-- Generated from ChapterHermiteLadderOrder.lean — theorem BookProof.HermiteLadder.pgLp_add'
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

theorem BookProof.HermiteLadder.pgLp_add_prime (p q : MvPolynomial (Fin d) ℂ) : pgLp (p + q) = pgLp p + pgLp q := by sorry
