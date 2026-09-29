-- Prove2me | Theorems.Thm_BookProof_HermiteBand_isBand2_weylProd
-- name    : BookProof.HermiteBand.isBand2_weylProd
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T12:34:47.464978+00:00
-- url     : https://prove2.me/theorems/b084ea22-e07f-490e-81c3-942c544501b4
-- title:
--   The Lean 4 theorem `isBand2_weylProd` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `isBand2_weylProd` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteBandCalculus.lean

-- Generated from ChapterHermiteBandCalculus.lean — theorem BookProof.HermiteBand.isBand2_weylProd
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
open BookProof.HermiteBand







noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

























open BookProof.NavierStokesFlow.DifferentialL2 BookProof.FullQuadratic

theorem BookProof.HermiteBand.isBand2_weylProd {S T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ}
    (hS : IsBand1 S) (hT : IsBand1 T) :
    IsBand2 (BookProof.YangMillsHermite.weylProd S T) := by sorry
