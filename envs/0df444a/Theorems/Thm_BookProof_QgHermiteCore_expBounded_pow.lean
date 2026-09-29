-- Prove2me | Theorems.Thm_BookProof_QgHermiteCore_expBounded_pow
-- name    : BookProof.QgHermiteCore.expBounded_pow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:22:37.618897+00:00
-- url     : https://prove2.me/theorems/e86f96ac-b178-4996-a515-637addd369d8
-- title:
--   (k : ℕ) : ExpBounded (fun x : ℝ => x ^ k)
-- statement:
--   Lean 4 theorem `BookProof.QgHermiteCore.expBounded_pow` (module `BookProof.QgHermiteCore`), source chapter `BookProof/ChapterQgHermiteCore.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterQgHermiteCore.lean

-- Generated from ChapterQgHermiteCore.lean — theorem BookProof.QgHermiteCore.expBounded_pow
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
open BookProof.QgHermiteCore













open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky







variable {E : Type*} [NormedAddCommGroup E]

theorem BookProof.QgHermiteCore.expBounded_pow (k : ℕ) : ExpBounded (fun x : ℝ => x ^ k) := by sorry
