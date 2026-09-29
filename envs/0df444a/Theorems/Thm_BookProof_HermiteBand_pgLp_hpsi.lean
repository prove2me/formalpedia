-- Prove2me | Theorems.Thm_BookProof_HermiteBand_pgLp_hpsi
-- name    : BookProof.HermiteBand.pgLp_hpsi
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T12:01:33.903493+00:00
-- url     : https://prove2.me/theorems/474f2fee-df01-4767-a2b8-d52689f98de5
-- title:
--   The Lean 4 theorem `pgLp_hpsi` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `pgLp_hpsi` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteBandCalculus.lean

-- Generated from ChapterHermiteBandCalculus.lean — theorem BookProof.HermiteBand.pgLp_hpsi
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
open BookProof.HermiteBand







noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

theorem BookProof.HermiteBand.pgLp_hpsi (α : Fin d →₀ ℕ) : pgLp (hpsi α) = hermiteMvLp α := by sorry
