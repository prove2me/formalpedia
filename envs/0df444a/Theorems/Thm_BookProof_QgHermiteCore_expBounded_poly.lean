-- Prove2me | Theorems.Thm_BookProof_QgHermiteCore_expBounded_poly
-- name    : BookProof.QgHermiteCore.expBounded_poly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T14:26:07.093753+00:00
-- url     : https://prove2.me/theorems/2e1de53d-8e0e-4fe4-ae20-6ce12b987da5
-- title:
--   (p : Polynomial ℝ) : ExpBounded (fun x => p.eval x)
-- statement:
--   Lean 4 theorem `BookProof.QgHermiteCore.expBounded_poly` (module `BookProof.QgHermiteCore`), source chapter `BookProof/ChapterQgHermiteCore.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterQgHermiteCore.lean

-- Generated from ChapterQgHermiteCore.lean — theorem BookProof.QgHermiteCore.expBounded_poly
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
open BookProof.QgHermiteCore













open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky







variable {E : Type*} [NormedAddCommGroup E]

theorem BookProof.QgHermiteCore.expBounded_poly (p : Polynomial ℝ) : ExpBounded (fun x => p.eval x) := by sorry
