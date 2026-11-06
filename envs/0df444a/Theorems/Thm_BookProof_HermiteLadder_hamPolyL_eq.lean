-- Prove2me | Theorems.Thm_BookProof_HermiteLadder_hamPolyL_eq
-- name    : BookProof.HermiteLadder.hamPolyL_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T14:45:49.8432+00:00
-- url     : https://prove2.me/theorems/da464671-3fa5-449f-afc0-43cd21ce41c5
-- title:
--   `BookProof.HermiteLadder.hamPolyL_eq` (S : Finset (Fin d)) (q : MvPolynomial (Fin d) ℂ) : hamPolyL S q = -(∑ j ∈ S, coreDL j ∘ₗ coreDL j) + mulL q
-- statement:
--   Prove the following Lean 4 theorem from `ChapterHermiteLadderOrder`.
--
--   `BookProof.HermiteLadder.hamPolyL_eq` (S : Finset (Fin d)) (q : MvPolynomial (Fin d) ℂ) : hamPolyL S q = -(∑ j ∈ S, coreDL j ∘ₗ coreDL j) + mulL q
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteLadder.hamPolyL_eq`.

-- Generated from ChapterHermiteLadderOrder.lean — theorem BookProof.HermiteLadder.hamPolyL_eq
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterDegSchrodingerCore
import Mathlib
import Definitions.Def_ChapterHermiteLadderOrder
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterFockWeightedSchurEsa
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterHermiteLadderShift
open BookProof.QgHermiteFriedrichs
open BookProof.HermiteLadder



open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs BookProof.DegSchrodinger
open scoped ENNReal

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteLadder.hamPolyL_eq (S : Finset (Fin d)) (q : MvPolynomial (Fin d) ℂ) :
    hamPolyL S q = -(∑ j ∈ S, coreDL j ∘ₗ coreDL j) + mulL q := by sorry
