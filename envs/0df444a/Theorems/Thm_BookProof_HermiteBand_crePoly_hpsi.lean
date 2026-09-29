-- Prove2me | Theorems.Thm_BookProof_HermiteBand_crePoly_hpsi
-- name    : BookProof.HermiteBand.crePoly_hpsi
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T11:59:52.883738+00:00
-- url     : https://prove2.me/theorems/39f1e789-e1f5-4c0a-b799-002054dd2cab
-- title:
--   The Lean 4 theorem `crePoly_hpsi` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `crePoly_hpsi` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteBandCalculus.lean

-- Generated from ChapterHermiteBandCalculus.lean — theorem BookProof.HermiteBand.crePoly_hpsi
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
open BookProof.HermiteBand







noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

theorem BookProof.HermiteBand.crePoly_hpsi (i : Fin d) (α : Fin d →₀ ℕ) :
    crePoly i (hpsi α) = ((Real.sqrt ((α i : ℝ) + 1) : ℝ) : ℂ) • hpsi (α + Finsupp.single i 1) := by sorry
