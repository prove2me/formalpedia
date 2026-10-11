-- Prove2me | Theorems.Thm_BookProof_ChapterSphericalPlancherel_oddSchwartz_odd
-- name    : BookProof.ChapterSphericalPlancherel.oddSchwartz_odd
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:22:22.336049+00:00
-- url     : https://prove2.me/theorems/d4f750f1-0c74-4c3a-b78a-b64b0e77caf3
-- title:
--   `BookProof.ChapterSphericalPlancherel.oddSchwartz_odd` (x : ℝ) : oddSchwartz (-x) = -oddSchwartz x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSphericalPlancherel`.
--
--   `BookProof.ChapterSphericalPlancherel.oddSchwartz_odd` (x : ℝ) : oddSchwartz (-x) = -oddSchwartz x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSphericalPlancherel.oddSchwartz_odd`.

-- Generated from ChapterSphericalPlancherel.lean — theorem BookProof.ChapterSphericalPlancherel.oddSchwartz_odd
import Definitions.Def_ChapterSphericalBessel
import Mathlib
import Definitions.Def_ChapterSphericalPlancherel
open BookProof.ChapterSphericalPlancherel



open MeasureTheory Set Real SchwartzMap
open scoped FourierTransform ContDiff
open BookProof.ChapterSphericalBessel

theorem BookProof.ChapterSphericalPlancherel.oddSchwartz_odd (x : ℝ) : oddSchwartz (-x) = -oddSchwartz x := by sorry
