-- Prove2me | Theorems.Thm_BookProof_HermiteCore_hermiteBasis_apply
-- name    : BookProof.HermiteCore.hermiteBasis_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:26:37.664652+00:00
-- url     : https://prove2.me/theorems/e1265d1b-a283-45f6-ac7d-cdc4aabb1c78
-- title:
--   The Lean 4 theorem `hermiteBasis_apply` in the `ChapterHermiteFunctions` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `hermiteBasis_apply` in the `ChapterHermiteFunctions` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteFunctions.lean

-- Generated from ChapterHermiteFunctions.lean — theorem BookProof.HermiteCore.hermiteBasis_apply
import Mathlib
import Definitions.Def_ChapterHermiteFunctions
open BookProof.HermiteCore








open MeasureTheory Polynomial Filter Topology FourierTransform SchwartzMap

noncomputable section

theorem BookProof.HermiteCore.hermiteBasis_apply (n : ℕ) : hermiteBasis n = hermiteLp n := by sorry
