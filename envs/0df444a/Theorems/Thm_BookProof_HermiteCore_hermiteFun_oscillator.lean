-- Prove2me | Theorems.Thm_BookProof_HermiteCore_hermiteFun_oscillator
-- name    : BookProof.HermiteCore.hermiteFun_oscillator
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:29:09.03599+00:00
-- url     : https://prove2.me/theorems/370f318c-d8a9-45e4-820d-8e781fe62e15
-- title:
--   The Lean 4 theorem `hermiteFun_oscillator` in the `ChapterHermiteFunctions` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `hermiteFun_oscillator` in the `ChapterHermiteFunctions` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteFunctions.lean

-- Generated from ChapterHermiteFunctions.lean — theorem BookProof.HermiteCore.hermiteFun_oscillator
import Mathlib
import Definitions.Def_ChapterHermiteFunctions
open BookProof.HermiteCore








open MeasureTheory Polynomial Filter Topology FourierTransform SchwartzMap

noncomputable section

theorem BookProof.HermiteCore.hermiteFun_oscillator (n : ℕ) (x : ℝ) :
    -(deriv (deriv (hermiteFun n)) x) + x ^ 2 / 4 * hermiteFun n x
      = ((n : ℝ) + 1 / 2) * hermiteFun n x := by sorry
