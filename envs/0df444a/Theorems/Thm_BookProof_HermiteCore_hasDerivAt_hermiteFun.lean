-- Prove2me | Theorems.Thm_BookProof_HermiteCore_hasDerivAt_hermiteFun
-- name    : BookProof.HermiteCore.hasDerivAt_hermiteFun
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:24:26.833752+00:00
-- url     : https://prove2.me/theorems/ba94ce87-cad5-49fd-9f84-c1d24e585258
-- title:
--   The Lean 4 theorem `hasDerivAt_hermiteFun` in the `ChapterHermiteFunctions` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `hasDerivAt_hermiteFun` in the `ChapterHermiteFunctions` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteFunctions.lean

-- Generated from ChapterHermiteFunctions.lean — theorem BookProof.HermiteCore.hasDerivAt_hermiteFun
import Mathlib
import Definitions.Def_ChapterHermiteFunctions
open BookProof.HermiteCore








open MeasureTheory Polynomial Filter Topology FourierTransform SchwartzMap

noncomputable section

theorem BookProof.HermiteCore.hasDerivAt_hermiteFun (n : ℕ) (x : ℝ) :
    HasDerivAt (hermiteFun n)
      (((derivative (hermiteR n)).eval x - x / 2 * (hermiteR n).eval x) * gaussH x) x := by sorry
