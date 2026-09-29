-- Prove2me | Theorems.Thm_BookProof_QgHermiteCore_ExpBounded_add
-- name    : BookProof.QgHermiteCore.ExpBounded.add
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:40:08.043437+00:00
-- url     : https://prove2.me/theorems/5451a373-2e92-4c22-a390-ee784632ac5f
-- title:
--   {f g : E → ℝ} (hf : ExpBounded f) (hg : ExpBounded g) : ExpBounded (fun x => f x + g x)
-- statement:
--   Lean 4 theorem `BookProof.QgHermiteCore.ExpBounded.add` (module `BookProof.QgHermiteCore`), source chapter `BookProof/ChapterQgHermiteCore.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterQgHermiteCore.lean

-- Generated from ChapterQgHermiteCore.lean — theorem BookProof.QgHermiteCore.ExpBounded.add
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
open BookProof.QgHermiteCore













open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky







variable {E : Type*} [NormedAddCommGroup E]

theorem BookProof.QgHermiteCore.ExpBounded.add {f g : E → ℝ} (hf : ExpBounded f) (hg : ExpBounded g) :
    ExpBounded (fun x => f x + g x) := by sorry
