-- Prove2me | Theorems.Thm_BookProof_HermiteBand_Band_mono
-- name    : BookProof.HermiteBand.Band.mono
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:11:04.870871+00:00
-- url     : https://prove2.me/theorems/7a94898e-7500-4ed2-8bcd-0e4273fac9d5
-- title:
--   The Lean 4 theorem `mono` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `mono` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteBandCalculus.lean

import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
-- Generated from ChapterHermiteBandCalculus.lean — theorem BookProof.HermiteBand.Band.mono
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterHermiteBandCalculus
open BookProof.HermiteBand







noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

theorem BookProof.HermiteBand.Band.mono {T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} {r M M' : ℕ}
    {C C' : ℝ} {g : ℕ → ℝ} (hg : ∀ n, 0 ≤ g n) (hM : M ≤ M') (hC : C ≤ C')
    (h : Band T r M C g) : Band T r M' C' g := by sorry
