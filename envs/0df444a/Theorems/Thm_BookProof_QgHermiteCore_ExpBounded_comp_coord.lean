-- Prove2me | Theorems.Thm_BookProof_QgHermiteCore_ExpBounded_comp_coord
-- name    : BookProof.QgHermiteCore.ExpBounded.comp_coord
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:41:40.043284+00:00
-- url     : https://prove2.me/theorems/07ef6f77-f3b0-4231-ac4e-a4c1b6e139c1
-- title:
--   {f : ℝ → ℝ} (hf : ExpBounded f) (i : Fin d) : ExpBounded (fun x : Vd d => f (x i))
-- statement:
--   Lean 4 theorem `BookProof.QgHermiteCore.ExpBounded.comp_coord` (module `BookProof.QgHermiteCore`), source chapter `BookProof/ChapterQgHermiteCore.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterQgHermiteCore.lean

-- Generated from ChapterQgHermiteCore.lean — theorem BookProof.QgHermiteCore.ExpBounded.comp_coord
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
open BookProof.QgHermiteCore













open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky







variable {E : Type*} [NormedAddCommGroup E]





































open BookProof.HermiteProductCore

variable {d : ℕ}

theorem BookProof.QgHermiteCore.ExpBounded.comp_coord {f : ℝ → ℝ} (hf : ExpBounded f) (i : Fin d) :
    ExpBounded (fun x : Vd d => f (x i)) := by sorry
