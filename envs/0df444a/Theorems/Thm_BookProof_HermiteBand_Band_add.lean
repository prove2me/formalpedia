-- Prove2me | Theorems.Thm_BookProof_HermiteBand_Band_add
-- name    : BookProof.HermiteBand.Band.add
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:10:48.524251+00:00
-- url     : https://prove2.me/theorems/42d02652-cbf9-428b-b6bc-4575f092147a
-- title:
--   The Lean 4 theorem `add` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `add` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteBandCalculus.lean

import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
-- Generated from ChapterHermiteBandCalculus.lean — theorem BookProof.HermiteBand.Band.add
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterHermiteBandCalculus
open BookProof.HermiteBand







noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

theorem BookProof.HermiteBand.Band.add {T S : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} {r M₁ M₂ : ℕ}
    {C₁ C₂ : ℝ} {g : ℕ → ℝ}
    (hT : Band T r M₁ C₁ g) (hS : Band S r M₂ C₂ g) :
    Band (T + S) r (M₁ + M₂) (C₁ + C₂) g := by sorry
