-- Prove2me | Theorems.Thm_BookProof_HermiteCore_hermiteR_ode
-- name    : BookProof.HermiteCore.hermiteR_ode
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:27:31.442984+00:00
-- url     : https://prove2.me/theorems/eeb7ece0-4ac1-4846-81c4-9de1e5a9d8b5
-- title:
--   The Lean 4 theorem `hermiteR_ode` in the `ChapterHermiteFunctions` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `hermiteR_ode` in the `ChapterHermiteFunctions` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteFunctions.lean

-- Generated from ChapterHermiteFunctions.lean — theorem BookProof.HermiteCore.hermiteR_ode
import Mathlib
import Definitions.Def_ChapterHermiteFunctions
open BookProof.HermiteCore








open MeasureTheory Polynomial Filter Topology FourierTransform SchwartzMap

noncomputable section

theorem BookProof.HermiteCore.hermiteR_ode (n : ℕ) :
    derivative (derivative (hermiteR n)) - X * derivative (hermiteR n) + C (n : ℝ) * hermiteR n
      = 0 := by sorry
