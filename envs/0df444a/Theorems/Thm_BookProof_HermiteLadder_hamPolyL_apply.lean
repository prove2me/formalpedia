-- Prove2me | Theorems.Thm_BookProof_HermiteLadder_hamPolyL_apply
-- name    : BookProof.HermiteLadder.hamPolyL_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T14:45:45.945343+00:00
-- url     : https://prove2.me/theorems/a16b8cf8-8255-49a4-9245-c6532557f1c2
-- title:
--   `BookProof.HermiteLadder.hamPolyL_apply` (S : Finset (Fin d)) (q p : MvPolynomial (Fin d) ℂ) : hamPolyL S q p = kinPolyS S p + q * p
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteLadderOrder`.
--
--   `BookProof.HermiteLadder.hamPolyL_apply` (S : Finset (Fin d)) (q p : MvPolynomial (Fin d) ℂ) : hamPolyL S q p = kinPolyS S p + q * p
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteLadder.hamPolyL_apply`.

-- Generated from ChapterHermiteLadderOrder.lean — theorem BookProof.HermiteLadder.hamPolyL_apply
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterDegSchrodingerCore
import Mathlib
import Definitions.Def_ChapterHermiteLadderOrder
import Definitions.Def_ChapterFockWeightedSchurEsa
import Definitions.Def_ChapterHermiteLadderShift
open BookProof.HermiteLadder



open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs BookProof.DegSchrodinger
open scoped ENNReal

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteLadder.hamPolyL_apply (S : Finset (Fin d)) (q p : MvPolynomial (Fin d) ℂ) :
    hamPolyL S q p = kinPolyS S p + q * p := by sorry
