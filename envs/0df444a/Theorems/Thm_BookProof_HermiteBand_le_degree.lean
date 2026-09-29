-- Prove2me | Theorems.Thm_BookProof_HermiteBand_le_degree
-- name    : BookProof.HermiteBand.le_degree
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T12:00:55.648908+00:00
-- url     : https://prove2.me/theorems/df21df0f-f6df-4e30-ac9b-84ece4dcdc61
-- title:
--   The Lean 4 theorem `le_degree` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `le_degree` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteBandCalculus.lean

-- Generated from ChapterHermiteBandCalculus.lean — theorem BookProof.HermiteBand.le_degree
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
open BookProof.HermiteBand







noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

theorem BookProof.HermiteBand.le_degree (α : Fin d →₀ ℕ) (i : Fin d) : α i ≤ α.degree := by sorry
