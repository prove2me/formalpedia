-- Prove2me | Theorems.Thm_BookProof_QgHermiteCore_expBounded_starobinskyV
-- name    : BookProof.QgHermiteCore.expBounded_starobinskyV
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:27:42.586395+00:00
-- url     : https://prove2.me/theorems/202578ac-e1e7-40dc-b210-923a43386b74
-- title:
--   (M alpha : ℝ) (hM : 0 < M) : ExpBounded (starobinskyV M alpha)
-- statement:
--   Lean 4 theorem `BookProof.QgHermiteCore.expBounded_starobinskyV` (module `BookProof.QgHermiteCore`), source chapter `BookProof/ChapterQgHermiteCore.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterQgHermiteCore.lean

-- Generated from ChapterQgHermiteCore.lean — theorem BookProof.QgHermiteCore.expBounded_starobinskyV
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
open BookProof.QgHermiteCore













open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky







variable {E : Type*} [NormedAddCommGroup E]

theorem BookProof.QgHermiteCore.expBounded_starobinskyV (M alpha : ℝ) (hM : 0 < M) :
    ExpBounded (starobinskyV M alpha) := by sorry
